// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Init Lean.Util.FindMVar Lean.Meta.ExprDefEq Lean.Meta.SynthInstance Lean.Meta.Tactic.Util
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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_restoreSynthInstanceCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_mkFreshExprMVarAt___spec__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
lean_object* l_Lean_Meta_synthAppInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object*);
lean_object* l_Lean_Meta_appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
lean_object* l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_importModules___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isExprMVarAssigned___at_Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_synthAppInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_saveAndResetSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
lean_object* l_Lean_isExprDefEq___at_Lean_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getFVarLocalDecl___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
lean_object* l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
lean_object* l_Lean_Meta_appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = l_Lean_Expr_getAppFn___main(x_2);
x_13 = l_Lean_Expr_isMVar(x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_3, x_4);
x_18 = l_Lean_getFVarLocalDecl___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__5(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_4 = x_26;
x_9 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_32 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(x_1, x_2, x_3, x_31, x_40, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main(x_21, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
lean_dec(x_4);
x_4 = x_61;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
lean_dec(x_4);
x_67 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(x_1, x_2, x_3, x_66, x_75, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isForall(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = l_Lean_Expr_getAppFn___main(x_1);
x_15 = l_Lean_Expr_isMVar(x_14);
lean_dec(x_14);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(x_3, x_4, x_5, x_6, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_8);
x_16 = lean_alloc_closure((void*)(l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2), 6, 1);
lean_closure_set(x_16, 0, x_8);
x_17 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1___boxed), 12, 6);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_7);
lean_closure_set(x_18, 2, x_17);
lean_closure_set(x_18, 3, x_2);
lean_closure_set(x_18, 4, x_3);
lean_closure_set(x_18, 5, x_4);
x_19 = lean_array_get_size(x_9);
x_20 = lean_nat_dec_lt(x_10, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(x_16, x_18, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
x_22 = lean_array_fget(x_9, x_10);
x_23 = l_Lean_getFVarLocalDecl___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__5(x_22, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_26);
x_27 = l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main(x_26, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 0:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_22);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_10, x_30);
lean_dec(x_10);
x_10 = x_31;
x_15 = x_29;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_10, x_35);
lean_dec(x_10);
x_37 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_11, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 2);
lean_inc(x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_22);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_46 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36, x_45, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_restoreSynthInstanceCache(x_38, x_11, x_12, x_13, x_14, x_48);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = l_Lean_restoreSynthInstanceCache(x_38, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
default: 
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_dec(x_27);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_62 = l___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main(x_26, x_11, x_12, x_13, x_14, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_22);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_10, x_65);
lean_dec(x_10);
x_10 = x_66;
x_15 = x_64;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_10, x_70);
lean_dec(x_10);
x_72 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_12, x_13, x_14, x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_11, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 2);
lean_inc(x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_22);
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_81 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_71, x_80, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_restoreSynthInstanceCache(x_73, x_11, x_12, x_13, x_14, x_83);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_restoreSynthInstanceCache(x_73, x_11, x_12, x_13, x_14, x_90);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_62);
if (x_96 == 0)
{
return x_62;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_62, 0);
x_98 = lean_ctor_get(x_62, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_62);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_27);
if (x_100 == 0)
{
return x_27;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_27, 0);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_27);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_23);
if (x_104 == 0)
{
return x_23;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_23, 0);
x_106 = lean_ctor_get(x_23, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_23);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = l_Lean_Expr_getAppFn___main(x_2);
x_13 = l_Lean_Expr_isMVar(x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_3, x_4);
x_18 = l_Lean_getFVarLocalDecl___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__5(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_4, x_25);
lean_dec(x_4);
x_4 = x_26;
x_9 = x_24;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_32 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 2);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_17);
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(x_1, x_2, x_3, x_31, x_40, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_restoreSynthInstanceCache(x_33, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main(x_21, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
lean_dec(x_4);
x_4 = x_61;
x_9 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_4, x_65);
lean_dec(x_4);
x_67 = l_Lean_saveAndResetSynthInstanceCache___rarg(x_6, x_7, x_8, x_63);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_5, 2);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_64);
lean_ctor_set(x_73, 1, x_17);
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(x_1, x_2, x_3, x_66, x_75, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_restoreSynthInstanceCache(x_68, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_57);
if (x_91 == 0)
{
return x_57;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_57, 0);
x_93 = lean_ctor_get(x_57, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_57);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
if (lean_obj_tag(x_6) == 7)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_29 = lean_array_get_size(x_4);
x_30 = lean_expr_instantiate_rev_range(x_26, x_5, x_29, x_4);
lean_dec(x_29);
lean_dec(x_26);
x_31 = l_Lean_mkFreshId___at_Lean_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = (uint8_t)((x_28 << 24) >> 61);
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_3, x_32, x_25, x_30, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_4, x_36);
x_3 = x_35;
x_4 = x_37;
x_6 = x_27;
x_11 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_4);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_46 = lean_expr_instantiate_rev_range(x_6, x_5, x_44, x_4);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_7, 1);
lean_dec(x_48);
lean_ctor_set(x_7, 1, x_3);
x_49 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(x_44, x_46, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 2);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_51);
x_53 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(x_44, x_46, x_4, x_5, x_52, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_46);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_6);
x_54 = lean_expr_instantiate_rev_range(x_40, x_5, x_44, x_4);
lean_dec(x_44);
lean_dec(x_40);
x_55 = l_Lean_mkFreshId___at_Lean_mkFreshExprMVarAt___spec__1___rarg(x_10, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = (uint8_t)((x_42 << 24) >> 61);
lean_inc(x_56);
x_59 = lean_local_ctx_mk_local_decl(x_3, x_56, x_39, x_54, x_58);
x_60 = l_Lean_mkFVar(x_56);
x_61 = lean_array_push(x_4, x_60);
x_3 = x_59;
x_4 = x_61;
x_6 = x_41;
x_11 = x_57;
goto _start;
}
}
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_12 = x_63;
goto block_24;
}
block_24:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
x_13 = lean_array_get_size(x_4);
x_14 = lean_expr_instantiate_rev_range(x_6, x_5, x_13, x_4);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_3);
if (x_1 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(x_13, x_14, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_3);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
if (x_1 == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(x_13, x_14, x_4, x_5, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_14);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_5);
lean_inc(x_4);
x_23 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_14, x_4, x_5, x_21, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isForall(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
x_14 = l_Lean_Expr_isMVar(x_13);
lean_dec(x_13);
x_15 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
x_16 = lean_box(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_8);
lean_dec(x_1);
x_18 = l_Lean_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = l_Array_empty___closed__1;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(x_21, x_2, x_19, x_22, x_23, x_10, x_3, x_4, x_5, x_6, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = l_Lean_Expr_isForall(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
x_29 = l_Lean_Expr_isMVar(x_28);
lean_dec(x_28);
x_30 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_FunInfo_6__getFunInfoAux___spec__2___closed__1;
x_31 = lean_box(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = l_Lean_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_3, x_4, x_5, x_6, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = l_Array_empty___closed__1;
x_39 = lean_unsigned_to_nat(0u);
x_40 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(x_37, x_2, x_35, x_38, x_39, x_25, x_3, x_4, x_5, x_6, x_36);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__1(x_1, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get_uint8(x_8, 0);
x_14 = lean_ctor_get_uint8(x_8, 1);
x_15 = lean_ctor_get_uint8(x_8, 2);
x_16 = lean_ctor_get_uint8(x_8, 3);
x_17 = lean_ctor_get_uint8(x_8, 4);
lean_dec(x_8);
x_18 = 2;
x_19 = lean_alloc_ctor(0, 0, 6);
lean_ctor_set_uint8(x_19, 0, x_13);
lean_ctor_set_uint8(x_19, 1, x_14);
lean_ctor_set_uint8(x_19, 2, x_15);
lean_ctor_set_uint8(x_19, 3, x_16);
lean_ctor_set_uint8(x_19, 4, x_17);
lean_ctor_set_uint8(x_19, 5, x_18);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__1(x_1, x_20, x_2, x_3, x_4, x_5, x_6);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_ctor_get_uint8(x_22, 0);
x_26 = lean_ctor_get_uint8(x_22, 1);
x_27 = lean_ctor_get_uint8(x_22, 2);
x_28 = lean_ctor_get_uint8(x_22, 3);
x_29 = lean_ctor_get_uint8(x_22, 4);
if (lean_is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
x_31 = 2;
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 0, 6);
} else {
 x_32 = x_30;
}
lean_ctor_set_uint8(x_32, 0, x_25);
lean_ctor_set_uint8(x_32, 1, x_26);
lean_ctor_set_uint8(x_32, 2, x_27);
lean_ctor_set_uint8(x_32, 3, x_28);
lean_ctor_set_uint8(x_32, 4, x_29);
lean_ctor_set_uint8(x_32, 5, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_24);
x_34 = lean_box(0);
x_35 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAux___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__1(x_1, x_34, x_33, x_3, x_4, x_5, x_6);
return x_35;
}
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__4(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
lean_object* l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_11__withNewLocalInstancesImpl___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___at___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unify");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_indentExpr(x_9);
x_11 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_MessageData_ofList___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_3);
x_18 = l_Lean_indentExpr(x_17);
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
x_21 = lean_box(0);
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_19, x_21, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign synthesized instance");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_26 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_25, x_7, x_8, x_9, x_10, x_11);
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
x_29 = l_Lean_Meta_synthInstanceImp(x_27, x_7, x_8, x_9, x_10, x_28);
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
x_32 = l_Lean_isExprDefEq___at_Lean_isDefEqNoConstantApprox___spec__1(x_25, x_30, x_7, x_8, x_9, x_10, x_31);
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
x_36 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3;
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
x_11 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_10, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_11;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_MetavarContext_renameMVar(x_12, x_1, x_2);
lean_ctor_set(x_9, 0, x_13);
x_14 = lean_st_ref_set(x_4, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_24 = l_Lean_MetavarContext_renameMVar(x_21, x_1, x_2);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
x_26 = lean_st_ref_set(x_4, x_25, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_20 = l_Lean_isExprMVarAssigned___at_Lean_Meta_synthPendingImp___spec__1(x_19, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Name_eraseMacroScopes(x_30);
lean_dec(x_30);
x_33 = l_Lean_Name_append___main(x_3, x_32);
x_34 = l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1(x_19, x_33, x_6, x_7, x_8, x_9, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_5 = x_14;
x_10 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_19);
lean_dec(x_14);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
lean_object* x_42; 
lean_dec(x_19);
lean_dec(x_16);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_dec(x_20);
x_5 = x_14;
x_10 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Name_isAnonymous(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
x_14 = lean_array_get_size(x_2);
lean_inc(x_14);
x_15 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2(x_2, x_3, x_11, x_14, x_14, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_14);
lean_dec(x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l_Lean_Name_isAnonymous(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_get_size(x_2);
lean_inc(x_20);
x_21 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2(x_2, x_3, x_17, x_20, x_20, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_20);
lean_dec(x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_renameMVar___at_Lean_Meta_appendParentTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forMAux___main___at_Lean_Meta_appendParentTag___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_8, x_3);
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
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_16, x_3);
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
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_24, x_3);
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
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_32, x_3);
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
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_33, x_35);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_15, x_6, x_7, x_8, x_9, x_10);
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
x_22 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_19, x_21);
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
x_31 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_28, x_30);
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
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(x_1, x_2, x_2, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_20 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_13, x_1, x_5, x_6, x_7, x_8, x_9);
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
x_36 = l___private_Lean_Meta_Tactic_Apply_4__dependsOnOthers(x_13, x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_importModules___closed__1;
x_9 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(x_1, x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_31 = l_Lean_isExprMVarAssigned___at_Lean_Meta_synthPendingImp___spec__1(x_30, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_apply___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_2, x_5, x_6, x_7, x_8, x_12);
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
x_16 = l___private_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_14, x_5, x_6, x_7, x_8, x_15);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(x_14, x_22, x_23, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_47; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
lean_inc(x_30);
x_47 = l_Lean_isExprDefEq___at_Lean_isDefEqNoConstantApprox___spec__1(x_30, x_11, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_30, x_11, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_30);
lean_dec(x_11);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_31 = x_56;
goto block_46;
}
}
else
{
uint8_t x_57; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
return x_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_46:
{
lean_object* x_32; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_32 = l_Lean_Meta_postprocessAppMVars(x_3, x_1, x_28, x_29, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_28, x_28, x_34, x_2);
x_36 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_1, x_35, x_5, x_6, x_7, x_8, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_28, x_34, x_34, x_5, x_6, x_7, x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_39, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_39);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 1);
lean_inc(x_65);
lean_dec(x_16);
x_66 = lean_ctor_get(x_17, 0);
lean_inc(x_66);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_67 = l___private_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_11, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_nat_sub(x_66, x_68);
lean_dec(x_68);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_73 = l_Lean_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(x_14, x_71, x_72, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_96; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
lean_inc(x_79);
x_96 = l_Lean_isExprDefEq___at_Lean_isDefEqNoConstantApprox___spec__1(x_79, x_11, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_79, x_11, x_5, x_6, x_7, x_8, x_99);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; 
lean_dec(x_79);
lean_dec(x_11);
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
lean_dec(x_96);
x_80 = x_105;
goto block_95;
}
}
else
{
uint8_t x_106; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_96);
if (x_106 == 0)
{
return x_96;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_96, 0);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_96);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
block_95:
{
lean_object* x_81; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_81 = l_Lean_Meta_postprocessAppMVars(x_3, x_1, x_77, x_78, x_5, x_6, x_7, x_8, x_80);
lean_dec(x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_77, x_77, x_83, x_2);
x_85 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_1, x_84, x_5, x_6, x_7, x_8, x_82);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_77, x_83, x_83, x_5, x_6, x_7, x_8, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l___private_Lean_Meta_Tactic_Apply_5__reorderNonDependentFirst(x_88, x_5, x_6, x_7, x_8, x_89);
lean_dec(x_88);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_81);
if (x_91 == 0)
{
return x_81;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_81, 0);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_81);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_73);
if (x_110 == 0)
{
return x_73;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_73, 0);
x_112 = lean_ctor_get(x_73, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_73);
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
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_67);
if (x_114 == 0)
{
return x_67;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_67, 0);
x_116 = lean_ctor_get(x_67, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_67);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_16);
if (x_118 == 0)
{
return x_16;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_16, 0);
x_120 = lean_ctor_get(x_16, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_13);
if (x_122 == 0)
{
return x_13;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_13, 0);
x_124 = lean_ctor_get(x_13, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_13);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_10);
if (x_126 == 0)
{
return x_10;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_10, 0);
x_128 = lean_ctor_get(x_10, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_10);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
lean_object* l_Lean_Meta_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_apply___lambda__1___boxed), 9, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_15, x_16, x_11, x_3, x_4, x_5, x_6, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_apply___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_apply___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7);
l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8 = _init_l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_synthAppInstances___spec__1___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
