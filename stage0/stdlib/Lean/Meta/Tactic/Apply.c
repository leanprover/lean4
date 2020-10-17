// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Init Lean.Util.FindMVar Lean.Meta.ExprDefEq Lean.Meta.SynthInstance Lean.Meta.CollectMVars Lean.Meta.Tactic.Util
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_apply_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply_match__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Meta_admit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
uint8_t l_List_elem___main___at_Lean_Meta_apply___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object*);
lean_object* l_Lean_Meta_apply___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_synthAppInstances___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_24__forallMetaTelescopeReducingAux___main(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs_match__1(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
lean_object* l_Lean_Meta_apply___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__2(lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Meta_apply___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Meta_checkNotAssigned___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1;
lean_object* l_Lean_Meta_getMVarsNoDelayed___at_Lean_Meta_apply___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2;
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
lean_object* l_Lean_Meta_getMVarsNoDelayedImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_importModules___closed__1;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_filterAux___main___at_Lean_Meta_apply___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1;
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_synthAppInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance___at_Lean_Meta_synthAppInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed___at_Lean_Meta_apply___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwTacticEx___rarg___closed__6;
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_setMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply_match__2(lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_apply___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_getAppFn___main(x_2);
x_10 = l_Lean_Expr_isMVar(x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 2;
lean_ctor_set_uint8(x_8, 5, x_10);
x_11 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1;
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_11, x_2, x_3, x_4, x_5, x_6);
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
else
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get_uint8(x_8, 0);
x_22 = lean_ctor_get_uint8(x_8, 1);
x_23 = lean_ctor_get_uint8(x_8, 2);
x_24 = lean_ctor_get_uint8(x_8, 3);
x_25 = lean_ctor_get_uint8(x_8, 4);
x_26 = lean_ctor_get_uint8(x_8, 6);
x_27 = lean_ctor_get_uint8(x_8, 7);
lean_dec(x_8);
x_28 = 2;
x_29 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_29, 0, x_21);
lean_ctor_set_uint8(x_29, 1, x_22);
lean_ctor_set_uint8(x_29, 2, x_23);
lean_ctor_set_uint8(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, 4, x_25);
lean_ctor_set_uint8(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, 6, x_26);
lean_ctor_set_uint8(x_29, 7, x_27);
lean_ctor_set(x_2, 0, x_29);
x_30 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1;
x_31 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_30, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_38 = x_31;
} else {
 lean_dec_ref(x_31);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_43 = lean_ctor_get_uint8(x_40, 0);
x_44 = lean_ctor_get_uint8(x_40, 1);
x_45 = lean_ctor_get_uint8(x_40, 2);
x_46 = lean_ctor_get_uint8(x_40, 3);
x_47 = lean_ctor_get_uint8(x_40, 4);
x_48 = lean_ctor_get_uint8(x_40, 6);
x_49 = lean_ctor_get_uint8(x_40, 7);
if (lean_is_exclusive(x_40)) {
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
x_51 = 2;
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 0, 8);
} else {
 x_52 = x_50;
}
lean_ctor_set_uint8(x_52, 0, x_43);
lean_ctor_set_uint8(x_52, 1, x_44);
lean_ctor_set_uint8(x_52, 2, x_45);
lean_ctor_set_uint8(x_52, 3, x_46);
lean_ctor_set_uint8(x_52, 4, x_47);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_48);
lean_ctor_set_uint8(x_52, 7, x_49);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
x_54 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1;
x_55 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_1, x_54, x_53, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unify");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nwith");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Lean_indentExpr(x_2);
x_10 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_indentExpr(x_3);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_throwTacticEx___rarg___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
x_19 = lean_box(0);
x_20 = l_Lean_Meta_throwTacticEx___rarg(x_18, x_1, x_17, x_19, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_synthAppInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_4, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_Meta_inferTypeRef;
x_20 = lean_st_ref_get(x_19, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_6(x_21, x_1, x_2, x_3, x_4, x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_26, 3, x_10);
x_27 = l_Lean_Meta_inferTypeRef;
x_28 = lean_st_ref_get(x_27, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_apply_6(x_29, x_1, x_2, x_3, x_26, x_5, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_32 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_33 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_32, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Meta_synthInstance___at_Lean_Meta_synthAppInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_synthAppInstances___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_236 = lean_st_ref_get(x_6, x_7);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 3);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_ctor_get_uint8(x_238, sizeof(void*)*1);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_241 = 0;
x_9 = x_241;
x_10 = x_240;
goto block_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
lean_dec(x_236);
x_243 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_244 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_243, x_3, x_4, x_5, x_6, x_242);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_unbox(x_245);
lean_dec(x_245);
x_9 = x_247;
x_10 = x_246;
goto block_235;
}
block_235:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_60; 
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_23);
x_24 = lean_st_ref_set(x_6, x_17, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_61);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_2);
lean_closure_set(x_63, 2, x_61);
x_64 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_65 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_64, x_63, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_6, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_6, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_70, 3);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_15);
x_76 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_61);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_15);
lean_ctor_set(x_70, 3, x_82);
x_83 = lean_st_ref_set(x_6, x_70, x_72);
lean_dec(x_6);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_61);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_87 = lean_ctor_get(x_70, 0);
x_88 = lean_ctor_get(x_70, 1);
x_89 = lean_ctor_get(x_70, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_70);
x_90 = lean_ctor_get(x_71, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_15);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_st_ref_set(x_6, x_93, x_72);
lean_dec(x_6);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_61);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_60, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
lean_dec(x_60);
x_26 = x_98;
x_27 = x_99;
goto block_59;
}
block_59:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_6, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 3);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_15);
x_37 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_26);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_15);
lean_ctor_set(x_31, 3, x_43);
x_44 = lean_st_ref_set(x_6, x_31, x_33);
lean_dec(x_6);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
x_50 = lean_ctor_get(x_31, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_52 = x_32;
} else {
 lean_dec_ref(x_32);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_15);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_6, x_54, x_33);
lean_dec(x_6);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_126; 
x_100 = lean_ctor_get(x_18, 0);
lean_inc(x_100);
lean_dec(x_18);
x_101 = 0;
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
lean_ctor_set(x_17, 3, x_102);
x_103 = lean_st_ref_set(x_6, x_17, x_19);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_127);
x_129 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_129, 0, x_1);
lean_closure_set(x_129, 1, x_2);
lean_closure_set(x_129, 2, x_127);
x_130 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_131 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_130, x_129, x_3, x_4, x_5, x_6, x_128);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_get(x_6, x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_take(x_6, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 2);
lean_inc(x_141);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 lean_ctor_release(x_136, 3);
 x_142 = x_136;
} else {
 lean_dec_ref(x_136);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 1);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 4, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_140);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_st_ref_set(x_6, x_146, x_138);
lean_dec(x_6);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_126, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_126, 1);
lean_inc(x_152);
lean_dec(x_126);
x_105 = x_151;
x_106 = x_152;
goto block_125;
}
block_125:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_107 = lean_st_ref_get(x_6, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_ref_take(x_6, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 2);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 1, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 4, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_st_ref_set(x_6, x_120, x_112);
lean_dec(x_6);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_184; 
x_153 = lean_ctor_get(x_17, 0);
x_154 = lean_ctor_get(x_17, 1);
x_155 = lean_ctor_get(x_17, 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_17);
x_156 = lean_ctor_get(x_18, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_157 = x_18;
} else {
 lean_dec_ref(x_18);
 x_157 = lean_box(0);
}
x_158 = 0;
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 1, 1);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set(x_160, 2, x_155);
lean_ctor_set(x_160, 3, x_159);
x_161 = lean_st_ref_set(x_6, x_160, x_19);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_184 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_185);
x_187 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_187, 0, x_1);
lean_closure_set(x_187, 1, x_2);
lean_closure_set(x_187, 2, x_185);
x_188 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_189 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_188, x_187, x_3, x_4, x_5, x_6, x_186);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_st_ref_get(x_6, x_190);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_st_ref_take(x_6, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 2);
lean_inc(x_199);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_200 = x_194;
} else {
 lean_dec_ref(x_194);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_195, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 1, 1);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_200)) {
 x_204 = lean_alloc_ctor(0, 4, 0);
} else {
 x_204 = x_200;
}
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_203);
x_205 = lean_st_ref_set(x_6, x_204, x_196);
lean_dec(x_6);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_185);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_184, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_184, 1);
lean_inc(x_210);
lean_dec(x_184);
x_163 = x_209;
x_164 = x_210;
goto block_183;
}
block_183:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_165 = lean_st_ref_get(x_6, x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_st_ref_take(x_6, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 2);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_176 = x_169;
} else {
 lean_dec_ref(x_169);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 4, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_177);
x_179 = lean_st_ref_set(x_6, x_178, x_170);
lean_dec(x_6);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
 lean_ctor_set_tag(x_182, 1);
}
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_5, 3);
lean_inc(x_211);
x_212 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_6, x_10);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_215 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_8, x_3, x_4, x_5, x_6, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_216);
x_218 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_218, 0, x_1);
lean_closure_set(x_218, 1, x_2);
lean_closure_set(x_218, 2, x_216);
x_219 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_220 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_219, x_218, x_3, x_4, x_5, x_6, x_217);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_213, x_219, x_211, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
lean_ctor_set(x_222, 0, x_216);
return x_222;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_215, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_215, 1);
lean_inc(x_228);
lean_dec(x_215);
x_229 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_230 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_213, x_229, x_211, x_3, x_4, x_5, x_6, x_228);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_230, 0);
lean_dec(x_232);
lean_ctor_set_tag(x_230, 1);
lean_ctor_set(x_230, 0, x_227);
return x_230;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_227);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign synthesized instance");
return x_1;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_6);
x_16 = lean_nat_sub(x_5, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = l_Lean_BinderInfo_inhabited;
x_19 = lean_box(x_18);
x_20 = lean_array_get(x_19, x_4, x_17);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = l_Lean_BinderInfo_isInstImplicit(x_21);
if (x_22 == 0)
{
lean_dec(x_17);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_3, x_17);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_26 = l_Lean_Meta_inferType___at_Lean_Meta_synthAppInstances___spec__1(x_25, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_29 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_27, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_synthAppInstances___spec__3(x_25, x_30, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_15);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_36, x_37, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_6 = x_15;
x_11 = x_43;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_29);
if (x_49 == 0)
{
return x_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_26);
if (x_53 == 0)
{
return x_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_11);
return x_58;
}
}
}
lean_object* l_Lean_Meta_synthAppInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_get_size(x_3);
lean_inc(x_10);
x_11 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4(x_1, x_2, x_3, x_4, x_10, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_11;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
x_15 = lean_nat_sub(x_4, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = l_Lean_Expr_Inhabited;
x_18 = lean_array_get(x_17, x_1, x_16);
x_19 = l_Lean_Expr_mvarId_x21(x_18);
lean_dec(x_18);
lean_inc(x_19);
x_20 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Meta_checkNotAssigned___spec__1(x_19, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_BinderInfo_inhabited;
x_25 = lean_box(x_24);
x_26 = lean_array_get(x_25, x_2, x_16);
lean_dec(x_16);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
x_28 = l_Lean_BinderInfo_isInstImplicit(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_19);
x_29 = l_Lean_Meta_getMVarTag(x_19, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_3);
x_32 = l_Lean_Meta_appendTag(x_3, x_30);
x_33 = l_Lean_Meta_setMVarTag(x_19, x_32, x_6, x_7, x_8, x_9, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_5 = x_14;
x_10 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_dec(x_19);
x_5 = x_14;
x_10 = x_23;
goto _start;
}
}
else
{
lean_object* x_41; 
lean_dec(x_19);
lean_dec(x_16);
x_41 = lean_ctor_get(x_20, 1);
lean_inc(x_41);
lean_dec(x_20);
x_5 = x_14;
x_10 = x_41;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
}
lean_object* l_Lean_Meta_appendParentTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getMVarTag(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Name_isAnonymous(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_9);
lean_inc(x_13);
x_17 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_11, x_13, x_13, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_13);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_free_object(x_9);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get(x_19, x_2, x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_23 = l_Lean_Meta_setMVarTag(x_22, x_11, x_4, x_5, x_6, x_7, x_12);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_array_get_size(x_2);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Name_isAnonymous(x_24);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_26);
x_30 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_2, x_3, x_24, x_26, x_26, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_33 = l_Lean_Expr_Inhabited;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get(x_33, x_2, x_34);
x_36 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
x_37 = l_Lean_Meta_setMVarTag(x_36, x_24, x_4, x_5, x_6, x_7, x_25);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_appendParentTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_Lean_Meta_synthAppInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Meta_appendParentTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_postprocessAppMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Expr_mvarId_x21(x_1);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_5, x_4);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_fget(x_3, x_5);
x_16 = lean_expr_eqv(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_inferType___at_Lean_Meta_synthAppInstances___spec__1(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_box(0);
x_22 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_19, x_21);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_17);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_5 = x_24;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_28, x_30);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_5 = x_33;
x_10 = x_29;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_15);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_5, x_42);
lean_dec(x_5);
x_5 = x_43;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2(x_1, x_2, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_fget(x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = l_Lean_Expr_mvarId_x21(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_13, x_1, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_array_push(x_17, x_19);
lean_ctor_set(x_4, 0, x_24);
x_3 = x_15;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_array_push(x_18, x_19);
lean_ctor_set(x_4, 1, x_27);
x_3 = x_15;
x_9 = x_26;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_free_object(x_4);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = l_Lean_Expr_mvarId_x21(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(x_13, x_1, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_array_push(x_33, x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
x_3 = x_15;
x_4 = x_41;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_array_push(x_34, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
x_3 = x_15;
x_4 = x_45;
x_9 = x_43;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_importModules___closed__1;
x_9 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1(x_1, x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_toList___rarg(x_12);
lean_dec(x_12);
x_15 = l_Array_toList___rarg(x_13);
lean_dec(x_13);
x_16 = l_List_append___rarg(x_14, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Array_toList___rarg(x_19);
lean_dec(x_19);
x_22 = l_Array_toList___rarg(x_20);
lean_dec(x_20);
x_23 = l_List_append___rarg(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_apply_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_apply_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_apply_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_apply_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_apply_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_apply_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 1;
x_10 = l_Array_empty___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_Basic_24__forallMetaTelescopeReducingAux___main(x_9, x_2, x_3, x_10, x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasMVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_MetavarContext_instantiateMVars(x_13, x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_3, x_10, x_11);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_25 = l_Lean_MetavarContext_instantiateMVars(x_22, x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_st_ref_set(x_3, x_28, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_array_fget(x_1, x_2);
x_30 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
x_31 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Meta_checkNotAssigned___spec__1(x_30, x_4, x_5, x_6, x_7, x_8);
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
x_13 = x_35;
x_14 = x_34;
goto block_28;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_13 = x_37;
x_14 = x_36;
goto block_28;
}
block_28:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_21 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_2 = x_20;
x_3 = x_21;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_array_fswap(x_1, x_2, x_3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_26 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_1 = x_23;
x_2 = x_25;
x_3 = x_26;
x_8 = x_14;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Meta_getMVarsNoDelayed___at_Lean_Meta_apply___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarsNoDelayedImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
uint8_t l_List_elem___main___at_Lean_Meta_apply___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Array_filterAux___main___at_Lean_Meta_apply___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = l_List_elem___main___at_Lean_Meta_apply___spec__5(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fswap(x_2, x_3, x_4);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_2 = x_15;
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_3 = x_21;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_apply___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_postprocessAppMVars(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2(x_5, x_7, x_8, x_9, x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_18 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_17, x_15);
x_19 = l_Lean_Meta_assignExprMVar___at_Lean_Meta_admit___spec__2(x_2, x_18, x_7, x_8, x_9, x_10, x_16);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3(x_3, x_17, x_17, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_getMVarsNoDelayedImp(x_15, x_7, x_8, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderNonDependentFirst(x_22, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Array_filterAux___main___at_Lean_Meta_apply___spec__6(x_29, x_25, x_17, x_17);
x_31 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_32 = l_List_append___rarg(x_29, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = l_Array_filterAux___main___at_Lean_Meta_apply___spec__6(x_33, x_25, x_17, x_17);
x_36 = l_Array_toList___rarg(x_35);
lean_dec(x_35);
x_37 = l_List_append___rarg(x_33, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Meta_apply___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
x_14 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1(x_1, x_13, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_21);
x_22 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_synthAppInstances___spec__3(x_21, x_2, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg(x_4, x_21, x_2, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
lean_dec(x_2);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_apply___lambda__1(x_3, x_4, x_19, x_20, x_5, x_32, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_20);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* l_Lean_Meta_apply___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_13 = l_Lean_Meta_inferType___at_Lean_Meta_synthAppInstances___spec__1(x_2, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_apply___lambda__2(x_14, x_11, x_3, x_1, x_2, x_21, x_22, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_26 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgs(x_11, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_sub(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_apply___lambda__2(x_14, x_11, x_3, x_1, x_2, x_29, x_30, x_5, x_6, x_7, x_8, x_28);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Meta_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_apply___lambda__3___boxed), 9, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__3___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_forallMetaTelescopeReducing___at_Lean_Meta_apply___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_apply___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_getMVarsNoDelayed___at_Lean_Meta_apply___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMVarsNoDelayed___at_Lean_Meta_apply___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_elem___main___at_Lean_Meta_apply___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Meta_apply___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_filterAux___main___at_Lean_Meta_apply___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___at_Lean_Meta_apply___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_apply___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_apply___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Meta_apply___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_apply___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Lean_Meta_apply___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_apply___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_CollectMVars(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_getExpectedNumArgsAux___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__1);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__2);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__3);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__4);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__5);
l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6 = _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___rarg___closed__6);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__4___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
