// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: Init Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint Lean.Elab.PreDefinition.WF.PackDomain Lean.Elab.PreDefinition.WF.PackMutual Lean.Elab.PreDefinition.WF.Rel Lean.Elab.PreDefinition.WF.Fix Lean.Elab.PreDefinition.WF.Eqns Lean.Elab.PreDefinition.WF.Ite
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_withFixedPrefix___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Elab_wfRecursion___closed__6;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_iteToDIte___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope(lean_object*);
lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__3;
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1;
lean_object* l_Lean_Elab_WF_mkUnaryArg_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_CasesOnApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2060_(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10;
static lean_object* l_Lean_Elab_wfRecursion___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__1___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(lean_object*, size_t, size_t);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_iteToDIte___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1;
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__2___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1;
lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_360_(uint8_t, uint8_t);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
static lean_object* l_Lean_Elab_getFixedPrefix___lambda__2___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
lean_object* l_panic___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_iteToDIte___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7;
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_withCommonTelescope___rarg___closed__1;
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1;
lean_object* l_Lean_Elab_WF_packDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_nat_dec_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Elab_instInhabitedPreDefinition;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = lean_ctor_get(x_16, 5);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed), 8, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_CasesOnApp_addArg___spec__2___rarg(x_17, x_18, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("args.size == 2\n            ", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1;
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PreDefinition.WF.Main", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Main.0.Lean.Elab.addNonRecPreDefs.mkSum", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5;
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_unsigned_to_nat(12u);
x_5 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSum", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8;
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inl", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8;
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_7);
x_19 = lean_array_get_size(x_6);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6;
x_23 = l_panic___at_Lean_Meta_whnfCore___spec__1(x_22, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_4, x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
x_27 = l_Lean_instInhabitedExpr;
x_28 = lean_array_get(x_27, x_6, x_25);
lean_inc(x_28);
x_29 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(x_1, x_2, x_3, x_26, x_28, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_26);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Expr_constLevels_x21(x_5);
x_33 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10;
x_34 = l_Lean_mkConst(x_33, x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get(x_27, x_6, x_35);
lean_dec(x_6);
x_37 = l_Lean_mkApp3(x_34, x_36, x_28, x_31);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = l_Lean_Expr_constLevels_x21(x_5);
x_41 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10;
x_42 = l_Lean_mkConst(x_41, x_40);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get(x_27, x_6, x_43);
lean_dec(x_6);
x_45 = l_Lean_mkApp3(x_42, x_44, x_28, x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_instInhabitedExpr;
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_array_get(x_51, x_6, x_52);
lean_inc(x_53);
x_54 = lean_apply_6(x_3, x_53, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_Expr_constLevels_x21(x_5);
x_58 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12;
x_59 = l_Lean_mkConst(x_58, x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_array_get(x_51, x_6, x_60);
lean_dec(x_6);
x_62 = l_Lean_mkApp3(x_59, x_53, x_61, x_56);
lean_ctor_set(x_54, 0, x_62);
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = l_Lean_Expr_constLevels_x21(x_5);
x_66 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12;
x_67 = l_Lean_mkConst(x_66, x_65);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_array_get(x_51, x_6, x_68);
lean_dec(x_6);
x_70 = l_Lean_mkApp3(x_67, x_53, x_69, x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_53);
lean_dec(x_6);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_54);
if (x_72 == 0)
{
return x_54;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_54, 0);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_54);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_dec_eq(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_whnfD(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux(x_16, x_18);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_nat_sub(x_19, x_12);
lean_dec(x_19);
x_23 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1(x_1, x_2, x_3, x_4, x_16, x_21, x_22, x_6, x_7, x_8, x_9, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
x_28 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Main.0.Lean.Elab.addNonRecPreDefs", 69);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = lean_unsigned_to_nat(102u);
x_5 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_array_get_size(x_6);
lean_inc(x_1);
lean_inc(x_6);
x_16 = l_Array_toSubarray___rarg(x_6, x_1, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnaryArg_go___boxed), 8, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_2, 4);
lean_inc(x_20);
lean_inc(x_6);
x_21 = l_Array_toSubarray___rarg(x_6, x_18, x_1);
x_22 = l_Array_ofSubarray___rarg(x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_22, x_18, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(x_3, x_4, x_19, x_18, x_26, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Lean_mkConst(x_30, x_5);
x_32 = l_Lean_mkAppN(x_31, x_22);
x_33 = l_Lean_mkApp(x_32, x_28);
x_34 = 0;
x_35 = 1;
x_36 = 1;
x_37 = l_Lean_Meta_mkLambdaFVars(x_6, x_33, x_34, x_35, x_36, x_10, x_11, x_12, x_13, x_29);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3;
x_44 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___spec__1(x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_23);
if (x_45 == 0)
{
return x_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_23, 0);
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_23);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_5);
lean_ctor_set(x_16, 4, x_6);
lean_ctor_set(x_16, 5, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_2);
x_17 = 0;
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_16, x_17, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_22 = l_Lean_Elab_instInhabitedPreDefinition;
x_23 = lean_array_get(x_22, x_1, x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_23, sizeof(void*)*6);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 5);
lean_inc(x_30);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_31 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed), 14, 5);
lean_closure_set(x_31, 0, x_3);
lean_closure_set(x_31, 1, x_2);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_6);
lean_closure_set(x_31, 4, x_4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_32 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___spec__1___rarg(x_30, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_83 = lean_st_ref_get(x_15, x_34);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 3);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_ctor_get_uint8(x_85, sizeof(void*)*1);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = 0;
x_36 = x_88;
x_37 = x_87;
goto block_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_35, x_10, x_11, x_12, x_13, x_14, x_15, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_36 = x_93;
x_37 = x_92;
goto block_82;
}
block_82:
{
if (x_36 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_24, x_25, x_26, x_27, x_28, x_29, x_33, x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_21;
x_6 = x_49;
x_9 = x_48;
x_16 = x_47;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc(x_28);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_28);
x_56 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_inc(x_33);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_33);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_35, x_62, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_66 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_24, x_25, x_26, x_27, x_28, x_29, x_33, x_64, x_10, x_11, x_12, x_13, x_14, x_15, x_65);
lean_dec(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_21;
x_6 = x_76;
x_9 = x_75;
x_16 = x_74;
goto _start;
}
}
else
{
uint8_t x_78; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
return x_66;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_66, 0);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_32);
if (x_94 == 0)
{
return x_32;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_32, 0);
x_96 = lean_ctor_get(x_32, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_32);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_9);
lean_ctor_set(x_98, 1, x_16);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_9);
lean_ctor_set(x_99, 1, x_16);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_12, x_13);
x_15 = lean_array_get_size(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_box(0);
lean_inc(x_15);
x_19 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(x_2, x_1, x_3, x_14, x_15, x_16, x_15, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_11 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_1, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(x_2, x_1, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Expr_bindingBody_x21(x_6);
lean_dec(x_6);
x_10 = lean_expr_instantiate1(x_9, x_1);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = l_Lean_Expr_bindingDomain_x21(x_13);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_1, x_16);
x_18 = l_Lean_Expr_bindingDomain_x21(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_Meta_isExprDefEq(x_14, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_bindingName_x21(x_13);
x_24 = l_Lean_Expr_bindingName_x21(x_17);
x_25 = lean_name_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_28 = l_Lean_Expr_binderInfo(x_13);
lean_dec(x_13);
x_29 = l_Lean_Expr_binderInfo(x_17);
lean_dec(x_17);
x_30 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_360_(x_28, x_29);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
uint8_t x_33; 
x_33 = lean_unbox(x_21);
lean_dec(x_21);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
size_t x_36; size_t x_37; 
lean_free_object(x_19);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_11 = x_22;
goto _start;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = l_Lean_Expr_bindingName_x21(x_13);
x_42 = l_Lean_Expr_bindingName_x21(x_17);
x_43 = lean_name_eq(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_47 = l_Lean_Expr_binderInfo(x_13);
lean_dec(x_13);
x_48 = l_Lean_Expr_binderInfo(x_17);
lean_dec(x_17);
x_49 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_360_(x_47, x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = lean_unbox(x_39);
lean_dec(x_39);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
return x_56;
}
else
{
size_t x_57; size_t x_58; 
x_57 = 1;
x_58 = lean_usize_add(x_3, x_57);
x_3 = x_58;
x_11 = x_40;
goto _start;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_19);
if (x_60 == 0)
{
return x_19;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_19, 0);
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_19);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_11);
return x_66;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isLambda(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_5);
x_13 = lean_array_push(x_1, x_5);
x_14 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(x_5, x_14, x_15, x_3);
lean_dec(x_5);
x_17 = l_Lean_Elab_withCommonTelescope_go___rarg(x_4, x_13, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_43; uint8_t x_44; 
x_11 = lean_array_get_size(x_3);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_11);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_12 = x_45;
goto block_42;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_11, x_11);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_12 = x_47;
goto block_42;
}
else
{
size_t x_48; size_t x_49; uint8_t x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_11);
x_50 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(x_3, x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_12 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
lean_dec(x_11);
x_52 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_52;
}
}
}
block_42:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_11);
if (x_14 == 0)
{
uint8_t x_26; 
x_26 = 1;
x_15 = x_26;
x_16 = x_10;
goto block_25;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_11, x_11);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = 1;
x_15 = x_28;
x_16 = x_10;
goto block_25;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_31 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(x_3, x_3, x_29, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = 1;
x_15 = x_35;
x_16 = x_34;
goto block_25;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_15 = x_37;
x_16 = x_36;
goto block_25;
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
block_25:
{
if (x_15 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
x_17 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_array_get(x_18, x_3, x_13);
x_20 = l_Lean_Expr_bindingName_x21(x_19);
x_21 = l_Lean_Expr_binderInfo(x_19);
x_22 = l_Lean_Expr_bindingDomain_x21(x_19);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope_go___rarg___lambda__1), 12, 4);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_11);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_1);
x_24 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_20, x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope_go___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_withCommonTelescope_go___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_withCommonTelescope_go___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_withCommonTelescope___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_withFixedPrefix___spec__1(x_11, x_12, x_1);
x_14 = l_Lean_Elab_withCommonTelescope___rarg___closed__1;
x_15 = l_Lean_Elab_withCommonTelescope_go___rarg(x_2, x_14, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withCommonTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withCommonTelescope___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_fget(x_17, x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_18, x_27);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_28);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 2;
x_37 = 0;
lean_ctor_set_uint8(x_29, 5, x_36);
lean_ctor_set_uint8(x_29, 9, x_37);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l_Lean_Meta_isExprDefEq(x_13, x_26, x_38, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_5, 0, x_44);
lean_ctor_set(x_39, 0, x_5);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_5, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_4 = x_50;
x_10 = x_48;
goto _start;
}
}
else
{
uint8_t x_52; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_ctor_get_uint8(x_29, 0);
x_57 = lean_ctor_get_uint8(x_29, 1);
x_58 = lean_ctor_get_uint8(x_29, 2);
x_59 = lean_ctor_get_uint8(x_29, 3);
x_60 = lean_ctor_get_uint8(x_29, 4);
x_61 = lean_ctor_get_uint8(x_29, 6);
x_62 = lean_ctor_get_uint8(x_29, 7);
x_63 = lean_ctor_get_uint8(x_29, 8);
x_64 = lean_ctor_get_uint8(x_29, 10);
x_65 = lean_ctor_get_uint8(x_29, 11);
x_66 = lean_ctor_get_uint8(x_29, 12);
x_67 = lean_ctor_get_uint8(x_29, 13);
lean_dec(x_29);
x_68 = 2;
x_69 = 0;
x_70 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_70, 0, x_56);
lean_ctor_set_uint8(x_70, 1, x_57);
lean_ctor_set_uint8(x_70, 2, x_58);
lean_ctor_set_uint8(x_70, 3, x_59);
lean_ctor_set_uint8(x_70, 4, x_60);
lean_ctor_set_uint8(x_70, 5, x_68);
lean_ctor_set_uint8(x_70, 6, x_61);
lean_ctor_set_uint8(x_70, 7, x_62);
lean_ctor_set_uint8(x_70, 8, x_63);
lean_ctor_set_uint8(x_70, 9, x_69);
lean_ctor_set_uint8(x_70, 10, x_64);
lean_ctor_set_uint8(x_70, 11, x_65);
lean_ctor_set_uint8(x_70, 12, x_66);
lean_ctor_set_uint8(x_70, 13, x_67);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_30);
lean_ctor_set(x_71, 2, x_31);
lean_ctor_set(x_71, 3, x_32);
lean_ctor_set(x_71, 4, x_33);
lean_ctor_set(x_71, 5, x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Lean_Meta_isExprDefEq(x_13, x_26, x_71, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_5, 0, x_77);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_5);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; size_t x_80; size_t x_81; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_80 = 1;
x_81 = lean_usize_add(x_4, x_80);
x_4 = x_81;
x_10 = x_79;
goto _start;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_15);
x_87 = lean_array_fget(x_17, x_18);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_18, x_88);
lean_dec(x_18);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_17);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_19);
x_91 = lean_ctor_get(x_6, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_6, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_6, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_6, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_6, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_6, 5);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_91, 0);
x_98 = lean_ctor_get_uint8(x_91, 1);
x_99 = lean_ctor_get_uint8(x_91, 2);
x_100 = lean_ctor_get_uint8(x_91, 3);
x_101 = lean_ctor_get_uint8(x_91, 4);
x_102 = lean_ctor_get_uint8(x_91, 6);
x_103 = lean_ctor_get_uint8(x_91, 7);
x_104 = lean_ctor_get_uint8(x_91, 8);
x_105 = lean_ctor_get_uint8(x_91, 10);
x_106 = lean_ctor_get_uint8(x_91, 11);
x_107 = lean_ctor_get_uint8(x_91, 12);
x_108 = lean_ctor_get_uint8(x_91, 13);
if (lean_is_exclusive(x_91)) {
 x_109 = x_91;
} else {
 lean_dec_ref(x_91);
 x_109 = lean_box(0);
}
x_110 = 2;
x_111 = 0;
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 0, 14);
} else {
 x_112 = x_109;
}
lean_ctor_set_uint8(x_112, 0, x_97);
lean_ctor_set_uint8(x_112, 1, x_98);
lean_ctor_set_uint8(x_112, 2, x_99);
lean_ctor_set_uint8(x_112, 3, x_100);
lean_ctor_set_uint8(x_112, 4, x_101);
lean_ctor_set_uint8(x_112, 5, x_110);
lean_ctor_set_uint8(x_112, 6, x_102);
lean_ctor_set_uint8(x_112, 7, x_103);
lean_ctor_set_uint8(x_112, 8, x_104);
lean_ctor_set_uint8(x_112, 9, x_111);
lean_ctor_set_uint8(x_112, 10, x_105);
lean_ctor_set_uint8(x_112, 11, x_106);
lean_ctor_set_uint8(x_112, 12, x_107);
lean_ctor_set_uint8(x_112, 13, x_108);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_92);
lean_ctor_set(x_113, 2, x_93);
lean_ctor_set(x_113, 3, x_94);
lean_ctor_set(x_113, 4, x_95);
lean_ctor_set(x_113, 5, x_96);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_114 = l_Lean_Meta_isExprDefEq(x_13, x_87, x_113, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
lean_ctor_set(x_5, 1, x_90);
lean_ctor_set(x_5, 0, x_119);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_5);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; size_t x_122; size_t x_123; 
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_dec(x_114);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_90);
lean_ctor_set(x_5, 0, x_1);
x_122 = 1;
x_123 = lean_usize_add(x_4, x_122);
x_4 = x_123;
x_10 = x_121;
goto _start;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_90);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_5, 1);
lean_inc(x_129);
lean_dec(x_5);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 2);
lean_inc(x_132);
x_133 = lean_nat_dec_lt(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_129);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_10);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
x_137 = lean_array_fget(x_130, x_131);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_131, x_138);
lean_dec(x_131);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_130);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_132);
x_141 = lean_ctor_get(x_6, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_6, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_6, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_6, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_6, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_6, 5);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_141, 0);
x_148 = lean_ctor_get_uint8(x_141, 1);
x_149 = lean_ctor_get_uint8(x_141, 2);
x_150 = lean_ctor_get_uint8(x_141, 3);
x_151 = lean_ctor_get_uint8(x_141, 4);
x_152 = lean_ctor_get_uint8(x_141, 6);
x_153 = lean_ctor_get_uint8(x_141, 7);
x_154 = lean_ctor_get_uint8(x_141, 8);
x_155 = lean_ctor_get_uint8(x_141, 10);
x_156 = lean_ctor_get_uint8(x_141, 11);
x_157 = lean_ctor_get_uint8(x_141, 12);
x_158 = lean_ctor_get_uint8(x_141, 13);
if (lean_is_exclusive(x_141)) {
 x_159 = x_141;
} else {
 lean_dec_ref(x_141);
 x_159 = lean_box(0);
}
x_160 = 2;
x_161 = 0;
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 0, 14);
} else {
 x_162 = x_159;
}
lean_ctor_set_uint8(x_162, 0, x_147);
lean_ctor_set_uint8(x_162, 1, x_148);
lean_ctor_set_uint8(x_162, 2, x_149);
lean_ctor_set_uint8(x_162, 3, x_150);
lean_ctor_set_uint8(x_162, 4, x_151);
lean_ctor_set_uint8(x_162, 5, x_160);
lean_ctor_set_uint8(x_162, 6, x_152);
lean_ctor_set_uint8(x_162, 7, x_153);
lean_ctor_set_uint8(x_162, 8, x_154);
lean_ctor_set_uint8(x_162, 9, x_161);
lean_ctor_set_uint8(x_162, 10, x_155);
lean_ctor_set_uint8(x_162, 11, x_156);
lean_ctor_set_uint8(x_162, 12, x_157);
lean_ctor_set_uint8(x_162, 13, x_158);
x_163 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_142);
lean_ctor_set(x_163, 2, x_143);
lean_ctor_set(x_163, 3, x_144);
lean_ctor_set(x_163, 4, x_145);
lean_ctor_set(x_163, 5, x_146);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_164 = l_Lean_Meta_isExprDefEq(x_13, x_137, x_163, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_140);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_167);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; size_t x_174; size_t x_175; 
x_172 = lean_ctor_get(x_164, 1);
lean_inc(x_172);
lean_dec(x_164);
lean_inc(x_1);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_140);
x_174 = 1;
x_175 = lean_usize_add(x_4, x_174);
x_4 = x_175;
x_5 = x_173;
x_10 = x_172;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_177 = lean_ctor_get(x_164, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_164, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_179 = x_164;
} else {
 lean_dec_ref(x_164);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_11, x_11);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(x_5, x_1, x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_27 = l_Lean_Expr_getAppNumArgsAux(x_5, x_12);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_29, x_31);
x_57 = lean_st_ref_get(x_9, x_10);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_4, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_array_get_size(x_32);
x_63 = lean_nat_dec_le(x_62, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
x_64 = lean_st_ref_set(x_4, x_60, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_33 = x_65;
goto block_56;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
x_66 = lean_st_ref_set(x_4, x_62, x_61);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_33 = x_67;
goto block_56;
}
block_56:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; 
x_34 = l_Array_toSubarray___rarg(x_2, x_12, x_3);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(x_35, x_32, x_38, x_21, x_36, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1;
x_44 = lean_box(0);
x_45 = lean_apply_6(x_43, x_44, x_6, x_7, x_8, x_9, x_42);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_48);
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___boxed), 10, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = l_Lean_Meta_forEachExpr_x27(x_5, x_15, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_9);
x_19 = lean_array_uget(x_6, x_8);
x_20 = lean_st_ref_get(x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_4, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_24, x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_22);
x_28 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_19, x_5, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = 1;
x_40 = lean_usize_add(x_8, x_39);
x_8 = x_40;
x_9 = x_38;
x_16 = x_37;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2;
lean_ctor_set(x_22, 0, x_46);
return x_22;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_47, x_49);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_19, x_5, x_51, x_10, x_11, x_12, x_13, x_14, x_15, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = 1;
x_61 = lean_usize_add(x_8, x_60);
x_8 = x_61;
x_9 = x_59;
x_16 = x_58;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_65 = x_52;
} else {
 lean_dec_ref(x_52);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_48);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_1, x_11);
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
}
static lean_object* _init_l_Lean_Elab_getFixedPrefix___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_11);
x_14 = lean_st_mk_ref(x_11, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_3);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Lean_Elab_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_11, x_15, x_20, x_3, x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_getFixedPrefix___lambda__1(x_15, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_15);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_getFixedPrefix___lambda__2), 10, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_withCommonTelescope___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_getFixedPrefix___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedPrefix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getFixedPrefix___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1;
x_16 = lean_array_push(x_15, x_14);
x_17 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_18 = l_Lean_Elab_applyAttributesOf(x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_box(0);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_9);
x_15 = l_Lean_Elab_addAsAxiom(x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Meta_transform___at_Lean_Meta_iteToDIte___spec__1(x_22, x_23, x_24, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_13, 5, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_29;
x_3 = x_30;
x_10 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_13);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
x_38 = lean_ctor_get(x_13, 1);
x_39 = lean_ctor_get(x_13, 2);
x_40 = lean_ctor_get(x_13, 3);
x_41 = lean_ctor_get(x_13, 4);
x_42 = lean_ctor_get(x_13, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_36);
lean_dec(x_13);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1;
x_44 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_transform___at_Lean_Meta_iteToDIte___spec__1(x_42, x_43, x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_39);
lean_ctor_set(x_48, 3, x_40);
lean_ctor_set(x_48, 4, x_41);
lean_ctor_set(x_48, 5, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*6, x_37);
x_49 = 1;
x_50 = lean_usize_add(x_2, x_49);
x_51 = lean_array_uset(x_15, x_2, x_48);
x_2 = x_50;
x_3 = x_51;
x_10 = x_47;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_55 = x_45;
} else {
 lean_dec_ref(x_45);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_st_ref_get(x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
x_19 = l_Lean_Elab_addAsAxiom(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_21 = l_Lean_Elab_WF_mkFix(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_wfRecursion___lambda__1___closed__1;
x_25 = l_Lean_Elab_wfRecursion___lambda__1___closed__2;
lean_inc(x_13);
lean_inc(x_12);
x_26 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_22, x_24, x_25, x_12, x_13, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_13, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_unfoldDeclsFrom(x_32, x_27, x_12, x_13, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_5);
lean_ctor_set(x_42, 4, x_6);
lean_ctor_set(x_42, 5, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_39);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_5);
lean_ctor_set(x_49, 4, x_6);
lean_ctor_set(x_49, 5, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*6, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_dec(x_26);
x_57 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = lean_ctor_get(x_21, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_dec(x_21);
x_64 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_63);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_19, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_dec(x_19);
x_71 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wfRel: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_29 = lean_st_ref_get(x_12, x_13);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_15 = x_34;
x_16 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_15 = x_39;
x_16 = x_38;
goto block_28;
}
block_28:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_wfRecursion___lambda__1(x_1, x_2, x_6, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_6);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_6);
x_20 = l_Lean_Elab_wfRecursion___lambda__2___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_14, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_wfRecursion___lambda__1(x_1, x_2, x_6, x_3, x_4, x_5, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Expr_bindingDomain_x21(x_8);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_inc(x_17);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lambda__2), 13, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_7);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_3);
x_19 = l_Lean_Elab_WF_elabWFRel___rarg(x_4, x_17, x_5, x_16, x_6, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_4, x_17, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(x_15, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_4, 3);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_15);
x_23 = l_Lean_Elab_WF_registerEqnsInfo(x_15, x_22, x_5, x_11, x_12, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_15);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(x_15, x_26, x_2, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_addAndCompilePartialRec(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_16 = l_Lean_Elab_WF_packDomain(x_4, x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_19 = l_Lean_Elab_WF_packMutual(x_4, x_3, x_17, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(">> ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fixed prefix: ", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_wfRecursion___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_67; lean_object* x_68; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_67 = lean_box(0);
lean_inc(x_8);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2(x_1, x_12, x_13, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_70 = l_Lean_Elab_getFixedPrefix(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_107 = lean_st_ref_get(x_9, x_72);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 3);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*1);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = 0;
x_74 = x_112;
x_75 = x_111;
goto block_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_73, x_4, x_5, x_6, x_7, x_8, x_9, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_unbox(x_115);
lean_dec(x_115);
x_74 = x_117;
x_75 = x_116;
goto block_106;
}
block_106:
{
if (x_74 == 0)
{
lean_object* x_76; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_76 = l_Lean_Elab_wfRecursion___lambda__5(x_12, x_13, x_1, x_71, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_18 = x_77;
x_19 = x_78;
goto block_66;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_71);
x_86 = l_Nat_repr(x_71);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_Elab_wfRecursion___closed__6;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_73, x_92, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_96 = l_Lean_Elab_wfRecursion___lambda__5(x_12, x_13, x_1, x_71, x_94, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
lean_dec(x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_18 = x_97;
x_19 = x_98;
goto block_66;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_100);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_dec(x_103);
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_99);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_ctor_get(x_70, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_70, 1);
lean_inc(x_119);
lean_dec(x_70);
x_120 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_119);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
lean_ctor_set_tag(x_120, 1);
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_68, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_68, 1);
lean_inc(x_126);
lean_dec(x_68);
x_127 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_126);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_66:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__4(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_21, 4);
lean_inc(x_24);
lean_inc(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_inc(x_23);
lean_inc(x_1);
lean_inc(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lambda__3___boxed), 15, 6);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_3);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_1);
lean_closure_set(x_26, 4, x_23);
lean_closure_set(x_26, 5, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_24, x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_51 = lean_st_ref_get(x_9, x_29);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_31 = x_56;
x_32 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_31 = x_61;
x_32 = x_60;
goto block_50;
}
block_50:
{
if (x_31 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Lean_Elab_wfRecursion___lambda__4(x_12, x_13, x_1, x_28, x_23, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_28, 3);
lean_inc(x_35);
x_36 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Elab_wfRecursion___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_wfRecursion___closed__4;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_28, 5);
lean_inc(x_41);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_30, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_wfRecursion___lambda__4(x_12, x_13, x_1, x_28, x_23, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_47);
return x_49;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_27);
if (x_62 == 0)
{
return x_27;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_wfRecursion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_wfRecursion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_wfRecursion___lambda__4(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_wfRecursion___lambda__5(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2060_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackDomain(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Ite(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackDomain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Ite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___lambda__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__4);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__5);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__6);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__7);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__8);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__9);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__10);
l_Lean_Elab_withCommonTelescope___rarg___closed__1 = _init_l_Lean_Elab_withCommonTelescope___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_withCommonTelescope___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_getFixedPrefix___spec__3___closed__2);
l_Lean_Elab_getFixedPrefix___lambda__2___closed__1 = _init_l_Lean_Elab_getFixedPrefix___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_getFixedPrefix___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_wfRecursion___spec__3___closed__2);
l_Lean_Elab_wfRecursion___lambda__1___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__1___closed__1);
l_Lean_Elab_wfRecursion___lambda__1___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__1___closed__2);
l_Lean_Elab_wfRecursion___lambda__2___closed__1 = _init_l_Lean_Elab_wfRecursion___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__2___closed__1);
l_Lean_Elab_wfRecursion___lambda__2___closed__2 = _init_l_Lean_Elab_wfRecursion___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___lambda__2___closed__2);
l_Lean_Elab_wfRecursion___closed__1 = _init_l_Lean_Elab_wfRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__1);
l_Lean_Elab_wfRecursion___closed__2 = _init_l_Lean_Elab_wfRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__2);
l_Lean_Elab_wfRecursion___closed__3 = _init_l_Lean_Elab_wfRecursion___closed__3();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__3);
l_Lean_Elab_wfRecursion___closed__4 = _init_l_Lean_Elab_wfRecursion___closed__4();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__4);
l_Lean_Elab_wfRecursion___closed__5 = _init_l_Lean_Elab_wfRecursion___closed__5();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__5);
l_Lean_Elab_wfRecursion___closed__6 = _init_l_Lean_Elab_wfRecursion___closed__6();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__6);
res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_2060_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
