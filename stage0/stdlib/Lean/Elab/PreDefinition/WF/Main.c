// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: Init Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint Lean.Elab.PreDefinition.WF.PackDomain Lean.Elab.PreDefinition.WF.PackMutual Lean.Elab.PreDefinition.WF.Rel Lean.Elab.PreDefinition.WF.Fix Lean.Elab.PreDefinition.WF.Eqns
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__12;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__11;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___closed__1;
lean_object* l_Lean_Elab_WF_mkUnaryArg_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_930_(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__10;
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_wfRecursion___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8;
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__9;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__8;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1;
lean_object* l_Lean_Elab_WF_packDomain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Elab_instInhabitedPreDefinition;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_1, x_14);
x_16 = lean_ctor_get(x_15, 5);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1;
x_18 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(x_16, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertion violation: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args.size == 2\n            ");
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
x_1 = lean_mk_string("Lean.Elab.PreDefinition.WF.Main");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Main.0.Lean.Elab.addNonRecPreDefs.mkSum");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__5;
x_3 = lean_unsigned_to_nat(39u);
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
x_1 = lean_mk_string("Sum");
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
x_1 = lean_mk_string("inr");
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
x_1 = lean_mk_string("inl");
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
static lean_object* _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnaryArg_go___boxed), 8, 2);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum(x_1, x_2, x_16, x_15, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 3);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_mkConst(x_20, x_5);
x_22 = l_Lean_mkApp(x_21, x_18);
x_23 = 0;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_6, x_22, x_23, x_24, x_10, x_11, x_12, x_13, x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_16, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1;
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1;
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wf");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4;
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1___boxed), 14, 5);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_6);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_32 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___spec__9___rarg(x_30, x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6;
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
x_39 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2(x_24, x_25, x_26, x_27, x_28, x_29, x_33, x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
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
x_56 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10;
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
x_66 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2(x_24, x_25, x_26, x_27, x_28, x_29, x_33, x_64, x_10, x_11, x_12, x_13, x_14, x_15, x_65);
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.WF.Main.0.Lean.Elab.addNonRecPreDefs");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs_mkSum___spec__1___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(27u);
x_4 = lean_unsigned_to_nat(54u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_box(0);
x_15 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2(x_2, x_1, x_12, x_15, x_16, x_17, x_16, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_29 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3;
x_30 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1(x_2, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_17 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_14);
x_19 = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs(x_14, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_14);
x_21 = l_Lean_Elab_addAndCompilePartialRec(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_4, 3);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l_Lean_Elab_WF_registerEqnsInfo(x_14, x_23, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> ");
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
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_18 = lean_box(0);
lean_inc(x_8);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_wfRecursion___spec__1(x_1, x_12, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l_Lean_Elab_WF_packDomain(x_1, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Elab_WF_packMutual(x_22, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_25);
x_29 = l_Lean_Elab_WF_elabWFRel(x_25, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_9, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_8);
x_36 = l_Lean_Elab_addAsAxiom(x_25, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Elab_WF_mkFix(x_25, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l_Lean_Elab_eraseRecAppSyntax(x_39, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6;
x_61 = lean_st_ref_get(x_9, x_45);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = 0;
x_47 = x_66;
x_48 = x_65;
goto block_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_47 = x_71;
x_48 = x_70;
goto block_60;
}
block_60:
{
if (x_47 == 0)
{
lean_object* x_49; 
x_49 = l_Lean_Elab_wfRecursion___lambda__1(x_12, x_13, x_1, x_44, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_wfRecursion___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_46, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_wfRecursion___lambda__1(x_12, x_13, x_1, x_44, x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_57);
return x_59;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_43);
if (x_72 == 0)
{
return x_43;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_43, 0);
x_74 = lean_ctor_get(x_43, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_43);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_1);
x_76 = lean_ctor_get(x_38, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 1);
lean_inc(x_77);
lean_dec(x_38);
x_78 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_1);
x_83 = lean_ctor_get(x_36, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_36, 1);
lean_inc(x_84);
lean_dec(x_36);
x_85 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_29);
if (x_90 == 0)
{
return x_29;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_29, 0);
x_92 = lean_ctor_get(x_29, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_29);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_24, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_24, 1);
lean_inc(x_95);
lean_dec(x_24);
x_96 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_21, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_21, 1);
lean_inc(x_102);
lean_dec(x_21);
x_103 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set_tag(x_103, 1);
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_19, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_19, 1);
lean_inc(x_109);
lean_dec(x_19);
x_110 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_109);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_wfRecursion___lambda__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_930_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackDomain(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackDomain(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_isOnlyOneUnaryDef___closed__1);
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
l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___lambda__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__4);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__5);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__6);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__7);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__8);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__9);
l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___spec__2___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_addNonRecPreDefs___lambda__1___closed__3);
l_Lean_Elab_wfRecursion___closed__1 = _init_l_Lean_Elab_wfRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__1);
l_Lean_Elab_wfRecursion___closed__2 = _init_l_Lean_Elab_wfRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_wfRecursion___closed__2);
res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_930_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
