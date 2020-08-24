// Lean compiler output
// Module: Lean.Meta.EqnCompiler.CaseValues
// Imports: Init Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Clear
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__2;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__3;
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__4;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__6;
lean_object* l_Lean_Meta_caseValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__2;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2;
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__1;
lean_object* l_Lean_Meta_CaseValueSubgoal_inhabited;
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6;
lean_object* l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__8;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__9;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__11;
lean_object* l_Lean_Meta_caseValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7;
lean_object* l_Lean_Meta_caseValue___closed__6;
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValue___closed__5;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__1;
lean_object* l_Lean_Meta_caseValueAux___lambda__2___closed__2;
lean_object* l_Lean_Meta_caseValue___closed__3;
lean_object* l_Lean_mkFreshExprMVar___at___private_Lean_Meta_Basic_7__forallMetaTelescopeReducingAux___main___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__10;
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__4(lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__5;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__7;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_CaseValueSubgoals_inhabited;
lean_object* l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1;
lean_object* l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__1;
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__3___closed__6;
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__3;
lean_object* l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValueAux___lambda__4___closed__5;
lean_object* _init_l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst domain: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Meta_FVarSubst_domain(x_1);
x_12 = l_List_toString___at_Lean_Meta_substCore___spec__4(x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_caseValueAux___lambda__2___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_2, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("found decl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("searching for decl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_caseValueAux___lambda__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_47; 
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
x_12 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_13 = x_50;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
lean_inc(x_4);
x_52 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_4, x_6, x_7, x_8, x_9, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_13 = x_55;
goto block_46;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = l_Lean_Meta_caseValueAux___lambda__3___closed__6;
lean_inc(x_4);
x_58 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_4, x_57, x_6, x_7, x_8, x_9, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_13 = x_59;
goto block_46;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_47, 0);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_46:
{
lean_object* x_14; 
x_14 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_apply_5(x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_4);
x_26 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_4, x_6, x_7, x_8, x_9, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_caseValueAux___lambda__3___closed__3;
x_37 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_4, x_36, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValue");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__4___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__4___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dite");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__4___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValueAux___lambda__4___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__1___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_caseValueAux___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = l_Lean_Meta_caseValueAux___lambda__4___closed__10;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_caseValueAux___lambda__4___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_1);
x_15 = l_Lean_Meta_getMVarType(x_1, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkFVar(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_Meta_mkEq(x_18, x_3, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_caseValueAux___lambda__4___closed__5;
lean_inc(x_20);
x_23 = l_Lean_mkApp(x_22, x_20);
x_24 = 0;
lean_inc(x_16);
lean_inc(x_20);
x_25 = l_Lean_mkForall(x_4, x_24, x_20, x_16);
x_26 = l_Lean_mkForall(x_4, x_24, x_23, x_16);
x_27 = 2;
lean_inc(x_6);
x_28 = l_Lean_mkFreshExprMVar___at___private_Lean_Meta_Basic_7__forallMetaTelescopeReducingAux___main___spec__1(x_25, x_6, x_27, x_7, x_8, x_9, x_10, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkFreshExprMVar___at___private_Lean_Meta_Basic_7__forallMetaTelescopeReducingAux___main___spec__1(x_26, x_6, x_27, x_7, x_8, x_9, x_10, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_20);
lean_inc(x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_29);
lean_inc(x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_38 = l_Lean_Meta_caseValueAux___lambda__4___closed__9;
x_39 = lean_array_push(x_38, x_35);
x_40 = lean_array_push(x_39, x_34);
x_41 = lean_array_push(x_40, x_36);
x_42 = lean_array_push(x_41, x_37);
x_43 = l_Lean_Meta_caseValueAux___lambda__4___closed__7;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Lean_Meta_mkAppOptM(x_43, x_42, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__4(x_1, x_45, x_7, x_8, x_9, x_10, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
x_50 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l_Lean_Meta_intro1(x_49, x_50, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
lean_inc(x_5);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_5);
x_57 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_58 = l_Lean_Meta_intro1(x_57, x_50, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_61);
x_63 = l_Lean_Meta_substCore(x_62, x_61, x_50, x_5, x_50, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_64, 1);
x_69 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
x_71 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_inc(x_67);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__2___boxed), 8, 2);
lean_closure_set(x_72, 0, x_67);
lean_closure_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_caseValueAux___lambda__4___closed__11;
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, x_72);
lean_inc(x_61);
lean_inc(x_67);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__3___boxed), 10, 4);
lean_closure_set(x_75, 0, x_67);
lean_closure_set(x_75, 1, x_61);
lean_closure_set(x_75, 2, x_70);
lean_closure_set(x_75, 3, x_71);
x_76 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_76, 0, x_74);
lean_closure_set(x_76, 1, x_75);
lean_inc(x_68);
x_77 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_68, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 4);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lean_Meta_withLocalContext___rarg(x_80, x_81, x_76, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
x_85 = l_Lean_Meta_FVarSubst_get(x_67, x_61);
x_86 = l_Lean_Expr_fvarId_x21(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_68);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_67);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 0, x_87);
lean_ctor_set(x_82, 0, x_64);
return x_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Meta_FVarSubst_get(x_67, x_61);
x_90 = l_Lean_Expr_fvarId_x21(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_67);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 0, x_91);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_64);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_free_object(x_64);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_56);
x_93 = !lean_is_exclusive(x_82);
if (x_93 == 0)
{
return x_82;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_82, 0);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_82);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_76);
lean_free_object(x_64);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_77);
if (x_97 == 0)
{
return x_77;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_77, 0);
x_99 = lean_ctor_get(x_77, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_77);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_101 = lean_ctor_get(x_64, 0);
x_102 = lean_ctor_get(x_64, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_64);
x_103 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_104 = lean_ctor_get(x_103, 2);
lean_inc(x_104);
x_105 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_inc(x_101);
x_106 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__2___boxed), 8, 2);
lean_closure_set(x_106, 0, x_101);
lean_closure_set(x_106, 1, x_105);
x_107 = l_Lean_Meta_caseValueAux___lambda__4___closed__11;
x_108 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_108, 0, x_107);
lean_closure_set(x_108, 1, x_106);
lean_inc(x_61);
lean_inc(x_101);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__3___boxed), 10, 4);
lean_closure_set(x_109, 0, x_101);
lean_closure_set(x_109, 1, x_61);
lean_closure_set(x_109, 2, x_104);
lean_closure_set(x_109, 3, x_105);
x_110 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_110, 0, x_108);
lean_closure_set(x_110, 1, x_109);
lean_inc(x_102);
x_111 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_102, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 4);
lean_inc(x_115);
lean_dec(x_112);
x_116 = l_Lean_Meta_withLocalContext___rarg(x_114, x_115, x_110, x_7, x_8, x_9, x_10, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Meta_FVarSubst_get(x_101, x_61);
x_120 = l_Lean_Expr_fvarId_x21(x_119);
lean_dec(x_119);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_102);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_101);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_56);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_61);
lean_dec(x_56);
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_126 = x_116;
} else {
 lean_dec_ref(x_116);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_110);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_130 = x_111;
} else {
 lean_dec_ref(x_111);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_132 = !lean_is_exclusive(x_63);
if (x_132 == 0)
{
return x_63;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_63, 0);
x_134 = lean_ctor_get(x_63, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_63);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_136 = !lean_is_exclusive(x_58);
if (x_136 == 0)
{
return x_58;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_58, 0);
x_138 = lean_ctor_get(x_58, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_58);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_140 = !lean_is_exclusive(x_51);
if (x_140 == 0)
{
return x_51;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_51, 0);
x_142 = lean_ctor_get(x_51, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_51);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_44);
if (x_144 == 0)
{
return x_44;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_44, 0);
x_146 = lean_ctor_get(x_44, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_44);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_19);
if (x_148 == 0)
{
return x_19;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_19, 0);
x_150 = lean_ctor_get(x_19, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_19);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_15);
if (x_152 == 0)
{
return x_15;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_15, 0);
x_154 = lean_ctor_get(x_15, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_15);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_13);
if (x_156 == 0)
{
return x_13;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_13, 0);
x_158 = lean_ctor_get(x_13, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_13);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
lean_object* l_Lean_Meta_caseValueAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_caseValueAux___lambda__4___boxed), 11, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 4);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_withLocalContext___rarg(x_17, x_18, x_13, x_6, x_7, x_8, x_9, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_caseValueAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_caseValueAux___lambda__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_caseValueAux___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_caseValueAux___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_caseValueAux___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("thenBranch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elseBranch");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_caseValue___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseValue___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_caseValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Meta_caseValueAux(x_1, x_2, x_3, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_caseValue___closed__4;
x_17 = l_Lean_Meta_appendTagSuffix(x_15, x_16, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_caseValue___closed__6;
x_22 = l_Lean_Meta_appendTagSuffix(x_20, x_21, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
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
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_CaseValueSubgoals_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Meta_FVarSubst_get(x_17, x_14);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_tryClear(x_5, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_16;
x_5 = x_21;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_dec(x_18);
x_4 = x_16;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("caseValues");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("list of values must not be empty");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2;
x_14 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_4, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Name_appendIndexAfter(x_1, x_3);
x_20 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_21 = l_Lean_Meta_caseValueAux(x_4, x_2, x_17, x_19, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 2);
lean_inc(x_28);
x_29 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7;
lean_inc(x_3);
x_30 = l_Lean_Name_appendIndexAfter(x_29, x_3);
lean_inc(x_26);
x_31 = l_Lean_Meta_appendTagSuffix(x_26, x_30, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(x_6, x_23, x_6, x_33, x_26, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_27);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_28);
x_40 = lean_array_push(x_7, x_39);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_45 = l_Lean_Name_appendIndexAfter(x_29, x_44);
lean_inc(x_41);
x_46 = l_Lean_Meta_appendTagSuffix(x_41, x_45, x_8, x_9, x_10, x_11, x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_array_push(x_6, x_42);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_20);
x_51 = lean_array_push(x_40, x_50);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_array_push(x_6, x_42);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_20);
x_55 = lean_array_push(x_40, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_3, x_61);
lean_dec(x_3);
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_dec(x_25);
x_65 = lean_array_push(x_6, x_64);
x_3 = x_62;
x_4 = x_63;
x_5 = x_18;
x_6 = x_65;
x_7 = x_40;
x_12 = x_36;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_34);
if (x_67 == 0)
{
return x_34;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_34, 0);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_34);
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
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_31);
if (x_71 == 0)
{
return x_31;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_31, 0);
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_31);
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
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Meta_caseValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_toList___rarg(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Array_empty___closed__1;
x_13 = l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main(x_4, x_2, x_11, x_1, x_10, x_12, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Meta_caseValues___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_caseValues(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_EqnCompiler_CaseValues(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_inhabited___closed__1);
l_Lean_Meta_CaseValueSubgoal_inhabited = _init_l_Lean_Meta_CaseValueSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoal_inhabited);
l_Lean_Meta_caseValueAux___lambda__2___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__1);
l_Lean_Meta_caseValueAux___lambda__2___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__2);
l_Lean_Meta_caseValueAux___lambda__2___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__2___closed__3);
l_Lean_Meta_caseValueAux___lambda__3___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__1);
l_Lean_Meta_caseValueAux___lambda__3___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__2);
l_Lean_Meta_caseValueAux___lambda__3___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__3);
l_Lean_Meta_caseValueAux___lambda__3___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__4);
l_Lean_Meta_caseValueAux___lambda__3___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__5);
l_Lean_Meta_caseValueAux___lambda__3___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__3___closed__6);
l_Lean_Meta_caseValueAux___lambda__4___closed__1 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__1);
l_Lean_Meta_caseValueAux___lambda__4___closed__2 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__2);
l_Lean_Meta_caseValueAux___lambda__4___closed__3 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__3);
l_Lean_Meta_caseValueAux___lambda__4___closed__4 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__4);
l_Lean_Meta_caseValueAux___lambda__4___closed__5 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__5);
l_Lean_Meta_caseValueAux___lambda__4___closed__6 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__6);
l_Lean_Meta_caseValueAux___lambda__4___closed__7 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__7);
l_Lean_Meta_caseValueAux___lambda__4___closed__8 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__8);
l_Lean_Meta_caseValueAux___lambda__4___closed__9 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__9);
l_Lean_Meta_caseValueAux___lambda__4___closed__10 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__10);
l_Lean_Meta_caseValueAux___lambda__4___closed__11 = _init_l_Lean_Meta_caseValueAux___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Meta_caseValueAux___lambda__4___closed__11);
l_Lean_Meta_caseValue___closed__1 = _init_l_Lean_Meta_caseValue___closed__1();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__1);
l_Lean_Meta_caseValue___closed__2 = _init_l_Lean_Meta_caseValue___closed__2();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__2);
l_Lean_Meta_caseValue___closed__3 = _init_l_Lean_Meta_caseValue___closed__3();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__3);
l_Lean_Meta_caseValue___closed__4 = _init_l_Lean_Meta_caseValue___closed__4();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__4);
l_Lean_Meta_caseValue___closed__5 = _init_l_Lean_Meta_caseValue___closed__5();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__5);
l_Lean_Meta_caseValue___closed__6 = _init_l_Lean_Meta_caseValue___closed__6();
lean_mark_persistent(l_Lean_Meta_caseValue___closed__6);
l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1 = _init_l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoals_inhabited___closed__1);
l_Lean_Meta_CaseValueSubgoals_inhabited = _init_l_Lean_Meta_CaseValueSubgoals_inhabited();
lean_mark_persistent(l_Lean_Meta_CaseValueSubgoals_inhabited);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__1);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__2);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__3);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__4);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__5);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__6);
l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7 = _init_l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_EqnCompiler_CaseValues_1__caseValuesAux___main___closed__7);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
