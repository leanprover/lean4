// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Apply
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
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__20;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__19;
lean_object* l_Lean_Meta_rewrite___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__7;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__10;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewrite___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__9;
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__11;
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__1;
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__8;
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__13;
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__16;
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_rewrite___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__18;
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__15;
lean_object* l_Lean_Meta_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__2;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__3;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__12;
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__14;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__6;
lean_object* l_List_map___main___at_Lean_Meta_rewrite___spec__3(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___closed__17;
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_30; 
x_30 = l_Lean_Expr_isFVar(x_2);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_9 = x_31;
goto block_29;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_box(0);
x_33 = l_Lean_Occurrences_beq(x_3, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_9 = x_34;
goto block_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = l_Lean_mkOptionalNode___closed__2;
x_36 = lean_array_push(x_35, x_2);
x_37 = lean_expr_abstract(x_1, x_36);
lean_dec(x_36);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
}
block_29:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_10 = l_Lean_Expr_toHeadIndex___main(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_st_mk_ref(x_13, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_10, x_12, x_1, x_11, x_15, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewrite___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_List_map___main___at_Lean_Meta_rewrite___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Expr_mvarId_x21(x_4);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_Expr_mvarId_x21(x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_rewrite___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality of iff proof expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive is not type correct");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find instance of the pattern in the target expression");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern is a metavariable ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("from equation");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__1___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propext");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__1___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewrite___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__1___closed__19;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(x_14, x_16, x_17, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_25, x_1);
x_27 = l_Lean_Expr_iff_x3f___closed__2;
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Expr_isAppOfArity___main(x_24, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_eq_x3f___closed__2;
x_31 = lean_unsigned_to_nat(3u);
x_32 = l_Lean_Expr_isAppOfArity___main(x_24, x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_33 = l_Lean_Meta_rewrite___lambda__1___closed__3;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_33, x_34, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_Expr_appFn_x21(x_24);
x_37 = l_Lean_Expr_appFn_x21(x_36);
x_38 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_39 = l_Lean_Expr_appArg_x21(x_36);
lean_dec(x_36);
x_40 = l_Lean_Expr_appArg_x21(x_24);
if (x_4 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Expr_getAppFn___main(x_39);
x_42 = l_Lean_Expr_isMVar(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
x_43 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_21);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_44);
x_46 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_44, x_39, x_6, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_113; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_113 = l_Lean_Expr_hasLooseBVars(x_47);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_114 = l_Lean_Meta_rewrite___lambda__1___closed__11;
x_115 = lean_box(0);
x_116 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_114, x_115, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
return x_116;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_116);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
else
{
x_49 = x_48;
goto block_112;
}
block_112:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_expr_instantiate1(x_47, x_40);
lean_dec(x_40);
x_51 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_50, x_8, x_9, x_10, x_11, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_44, 2);
x_54 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_44, x_44, x_8, x_9, x_10, x_11, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Expr_appFn_x21(x_55);
lean_dec(x_55);
x_58 = l_Lean_mkApp(x_57, x_47);
x_59 = l_Lean_Meta_rewrite___lambda__1___closed__5;
x_60 = 0;
x_61 = l_Lean_mkLambda(x_59, x_60, x_38, x_58);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_61);
x_96 = l_Lean_Meta_isTypeCorrect(x_61, x_8, x_9, x_10, x_11, x_56);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_Meta_rewrite___lambda__1___closed__8;
x_101 = lean_box(0);
x_102 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_100, x_101, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_dec(x_96);
x_62 = x_107;
goto block_95;
}
block_95:
{
lean_object* x_63; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_63 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_44, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_66 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_61, x_64, x_26, x_8, x_9, x_10, x_11, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_23);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = l_Array_toList___rarg(x_73);
lean_dec(x_73);
x_75 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_74);
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_52);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_71, 0, x_76);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = l_Array_toList___rarg(x_77);
lean_dec(x_77);
x_80 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_52);
lean_ctor_set(x_81, 1, x_67);
lean_ctor_set(x_81, 2, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_67);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_83 = !lean_is_exclusive(x_69);
if (x_83 == 0)
{
return x_69;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_69, 0);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_69);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_52);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_66);
if (x_87 == 0)
{
return x_66;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_66, 0);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_66);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_63);
if (x_91 == 0)
{
return x_63;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_63, 0);
x_93 = lean_ctor_get(x_63, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_63);
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
uint8_t x_108; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_54);
if (x_108 == 0)
{
return x_54;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_54, 0);
x_110 = lean_ctor_get(x_54, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_54);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_46);
if (x_121 == 0)
{
return x_46;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_46, 0);
x_123 = lean_ctor_get(x_46, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_46);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_125 = l_Lean_indentExpr(x_39);
x_126 = l_Lean_Meta_rewrite___lambda__1___closed__14;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_MessageData_ofList___closed__3;
x_129 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Meta_rewrite___lambda__1___closed__17;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_indentExpr(x_24);
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_box(0);
x_135 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_133, x_134, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
return x_135;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; 
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_140 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_26, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_227; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_40);
x_227 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_40, x_39, x_8, x_9, x_10, x_11, x_142);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Expr_getAppFn___main(x_40);
x_231 = l_Lean_Expr_isMVar(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
lean_dec(x_228);
x_143 = x_229;
goto block_226;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
lean_dec(x_141);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_232 = l_Lean_indentExpr(x_40);
x_233 = l_Lean_Meta_rewrite___lambda__1___closed__14;
x_234 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_MessageData_ofList___closed__3;
x_236 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Meta_rewrite___lambda__1___closed__17;
x_238 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_indentExpr(x_228);
x_240 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_box(0);
x_242 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_240, x_241, x_8, x_9, x_10, x_11, x_229);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
return x_242;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_242, 0);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_242);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_141);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_247 = !lean_is_exclusive(x_227);
if (x_247 == 0)
{
return x_227;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_227, 0);
x_249 = lean_ctor_get(x_227, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_227);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
block_226:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_145);
x_147 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_145, x_40, x_6, x_8, x_9, x_10, x_11, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_214; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_214 = l_Lean_Expr_hasLooseBVars(x_148);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
x_215 = l_Lean_Meta_rewrite___lambda__1___closed__11;
x_216 = lean_box(0);
x_217 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_215, x_216, x_8, x_9, x_10, x_11, x_149);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
return x_217;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_217);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
x_150 = x_149;
goto block_213;
}
block_213:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_expr_instantiate1(x_148, x_39);
lean_dec(x_39);
x_152 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_151, x_8, x_9, x_10, x_11, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_145, 2);
x_155 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_145, x_145, x_8, x_9, x_10, x_11, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_appFn_x21(x_156);
lean_dec(x_156);
x_159 = l_Lean_mkApp(x_158, x_148);
x_160 = l_Lean_Meta_rewrite___lambda__1___closed__5;
x_161 = 0;
x_162 = l_Lean_mkLambda(x_160, x_161, x_38, x_159);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_162);
x_197 = l_Lean_Meta_isTypeCorrect(x_162, x_8, x_9, x_10, x_11, x_157);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_162);
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_23);
lean_dec(x_22);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = l_Lean_Meta_rewrite___lambda__1___closed__8;
x_202 = lean_box(0);
x_203 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_201, x_202, x_8, x_9, x_10, x_11, x_200);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_203);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
else
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_197, 1);
lean_inc(x_208);
lean_dec(x_197);
x_163 = x_208;
goto block_196;
}
block_196:
{
lean_object* x_164; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_164 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_145, x_8, x_9, x_10, x_11, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_167 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_162, x_165, x_141, x_8, x_9, x_10, x_11, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_170 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_169);
lean_dec(x_23);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_171);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = l_Array_toList___rarg(x_174);
lean_dec(x_174);
x_176 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_175);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_153);
lean_ctor_set(x_177, 1, x_168);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_172, 0, x_177);
return x_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_172);
x_180 = l_Array_toList___rarg(x_178);
lean_dec(x_178);
x_181 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_180);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_153);
lean_ctor_set(x_182, 1, x_168);
lean_ctor_set(x_182, 2, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_168);
lean_dec(x_153);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_184 = !lean_is_exclusive(x_170);
if (x_184 == 0)
{
return x_170;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_170, 0);
x_186 = lean_ctor_get(x_170, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_170);
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
lean_dec(x_153);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_167);
if (x_188 == 0)
{
return x_167;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_167, 0);
x_190 = lean_ctor_get(x_167, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_167);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_162);
lean_dec(x_153);
lean_dec(x_141);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_164);
if (x_192 == 0)
{
return x_164;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_164, 0);
x_194 = lean_ctor_get(x_164, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_164);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_209 = !lean_is_exclusive(x_155);
if (x_209 == 0)
{
return x_155;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_155, 0);
x_211 = lean_ctor_get(x_155, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_155);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_147);
if (x_222 == 0)
{
return x_147;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_147, 0);
x_224 = lean_ctor_get(x_147, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_147);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_251 = !lean_is_exclusive(x_140);
if (x_251 == 0)
{
return x_140;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_140, 0);
x_253 = lean_ctor_get(x_140, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_140);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = l_Lean_Expr_appFn_x21(x_24);
x_256 = l_Lean_Expr_appArg_x21(x_255);
lean_dec(x_255);
x_257 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_257);
lean_inc(x_256);
x_258 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_256, x_257, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_Meta_rewrite___lambda__1___closed__20;
x_262 = l_Lean_mkApp3(x_261, x_256, x_257, x_26);
x_263 = l_Lean_Expr_eq_x3f___closed__2;
x_264 = lean_unsigned_to_nat(3u);
x_265 = l_Lean_Expr_isAppOfArity___main(x_259, x_263, x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_266 = l_Lean_Meta_rewrite___lambda__1___closed__3;
x_267 = lean_box(0);
x_268 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_266, x_267, x_8, x_9, x_10, x_11, x_260);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = l_Lean_Expr_appFn_x21(x_259);
x_270 = l_Lean_Expr_appFn_x21(x_269);
x_271 = l_Lean_Expr_appArg_x21(x_270);
lean_dec(x_270);
x_272 = l_Lean_Expr_appArg_x21(x_269);
lean_dec(x_269);
x_273 = l_Lean_Expr_appArg_x21(x_259);
if (x_4 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = l_Lean_Expr_getAppFn___main(x_272);
x_275 = l_Lean_Expr_isMVar(x_274);
lean_dec(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_259);
x_276 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_260);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_277);
x_279 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_277, x_272, x_6, x_8, x_9, x_10, x_11, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_346; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_346 = l_Lean_Expr_hasLooseBVars(x_280);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
x_347 = l_Lean_Meta_rewrite___lambda__1___closed__11;
x_348 = lean_box(0);
x_349 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_347, x_348, x_8, x_9, x_10, x_11, x_281);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
return x_349;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
else
{
x_282 = x_281;
goto block_345;
}
block_345:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_expr_instantiate1(x_280, x_273);
lean_dec(x_273);
x_284 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_283, x_8, x_9, x_10, x_11, x_282);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_277, 2);
x_287 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_277, x_277, x_8, x_9, x_10, x_11, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_Expr_appFn_x21(x_288);
lean_dec(x_288);
x_291 = l_Lean_mkApp(x_290, x_280);
x_292 = l_Lean_Meta_rewrite___lambda__1___closed__5;
x_293 = 0;
x_294 = l_Lean_mkLambda(x_292, x_293, x_271, x_291);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_294);
x_329 = l_Lean_Meta_isTypeCorrect(x_294, x_8, x_9, x_10, x_11, x_289);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec(x_294);
lean_dec(x_285);
lean_dec(x_277);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
lean_dec(x_329);
x_333 = l_Lean_Meta_rewrite___lambda__1___closed__8;
x_334 = lean_box(0);
x_335 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_333, x_334, x_8, x_9, x_10, x_11, x_332);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
return x_335;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_335, 0);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_335);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
else
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_329, 1);
lean_inc(x_340);
lean_dec(x_329);
x_295 = x_340;
goto block_328;
}
block_328:
{
lean_object* x_296; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_296 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_277, x_8, x_9, x_10, x_11, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_299 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_294, x_297, x_262, x_8, x_9, x_10, x_11, x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_302 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_301);
lean_dec(x_23);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_303);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = l_Array_toList___rarg(x_306);
lean_dec(x_306);
x_308 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_307);
x_309 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_309, 0, x_285);
lean_ctor_set(x_309, 1, x_300);
lean_ctor_set(x_309, 2, x_308);
lean_ctor_set(x_304, 0, x_309);
return x_304;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_304, 0);
x_311 = lean_ctor_get(x_304, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_304);
x_312 = l_Array_toList___rarg(x_310);
lean_dec(x_310);
x_313 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_312);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_285);
lean_ctor_set(x_314, 1, x_300);
lean_ctor_set(x_314, 2, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_311);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec(x_300);
lean_dec(x_285);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_316 = !lean_is_exclusive(x_302);
if (x_316 == 0)
{
return x_302;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_302, 0);
x_318 = lean_ctor_get(x_302, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_302);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_285);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_320 = !lean_is_exclusive(x_299);
if (x_320 == 0)
{
return x_299;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_299, 0);
x_322 = lean_ctor_get(x_299, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_299);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_294);
lean_dec(x_285);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_324 = !lean_is_exclusive(x_296);
if (x_324 == 0)
{
return x_296;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_296, 0);
x_326 = lean_ctor_get(x_296, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_296);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_285);
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_341 = !lean_is_exclusive(x_287);
if (x_341 == 0)
{
return x_287;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_287, 0);
x_343 = lean_ctor_get(x_287, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_287);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_277);
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_354 = !lean_is_exclusive(x_279);
if (x_354 == 0)
{
return x_279;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_279, 0);
x_356 = lean_ctor_get(x_279, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_279);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_358 = l_Lean_indentExpr(x_272);
x_359 = l_Lean_Meta_rewrite___lambda__1___closed__14;
x_360 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
x_361 = l_Lean_MessageData_ofList___closed__3;
x_362 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Lean_Meta_rewrite___lambda__1___closed__17;
x_364 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Lean_indentExpr(x_259);
x_366 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_box(0);
x_368 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_366, x_367, x_8, x_9, x_10, x_11, x_260);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
return x_368;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_368, 0);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_368);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
lean_object* x_373; 
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_373 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_262, x_8, x_9, x_10, x_11, x_260);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_460; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_272);
lean_inc(x_273);
x_460 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_273, x_272, x_8, x_9, x_10, x_11, x_375);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = l_Lean_Expr_getAppFn___main(x_273);
x_464 = l_Lean_Expr_isMVar(x_463);
lean_dec(x_463);
if (x_464 == 0)
{
lean_dec(x_461);
x_376 = x_462;
goto block_459;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
lean_dec(x_374);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_465 = l_Lean_indentExpr(x_273);
x_466 = l_Lean_Meta_rewrite___lambda__1___closed__14;
x_467 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_465);
x_468 = l_Lean_MessageData_ofList___closed__3;
x_469 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = l_Lean_Meta_rewrite___lambda__1___closed__17;
x_471 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = l_Lean_indentExpr(x_461);
x_473 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
x_474 = lean_box(0);
x_475 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_473, x_474, x_8, x_9, x_10, x_11, x_462);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_476 = !lean_is_exclusive(x_475);
if (x_476 == 0)
{
return x_475;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_475, 0);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_475);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_374);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_480 = !lean_is_exclusive(x_460);
if (x_480 == 0)
{
return x_460;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_460, 0);
x_482 = lean_ctor_get(x_460, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_460);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
block_459:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_377 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_378);
x_380 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_378, x_273, x_6, x_8, x_9, x_10, x_11, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_447; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_447 = l_Lean_Expr_hasLooseBVars(x_381);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_374);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
x_448 = l_Lean_Meta_rewrite___lambda__1___closed__11;
x_449 = lean_box(0);
x_450 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_448, x_449, x_8, x_9, x_10, x_11, x_382);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_451 = !lean_is_exclusive(x_450);
if (x_451 == 0)
{
return x_450;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_450, 0);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_450);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
else
{
x_383 = x_382;
goto block_446;
}
block_446:
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_384 = lean_expr_instantiate1(x_381, x_272);
lean_dec(x_272);
x_385 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_384, x_8, x_9, x_10, x_11, x_383);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_378, 2);
x_388 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_378, x_378, x_8, x_9, x_10, x_11, x_387);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_Expr_appFn_x21(x_389);
lean_dec(x_389);
x_392 = l_Lean_mkApp(x_391, x_381);
x_393 = l_Lean_Meta_rewrite___lambda__1___closed__5;
x_394 = 0;
x_395 = l_Lean_mkLambda(x_393, x_394, x_271, x_392);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_395);
x_430 = l_Lean_Meta_isTypeCorrect(x_395, x_8, x_9, x_10, x_11, x_390);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_unbox(x_431);
lean_dec(x_431);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_378);
lean_dec(x_374);
lean_dec(x_23);
lean_dec(x_22);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
lean_dec(x_430);
x_434 = l_Lean_Meta_rewrite___lambda__1___closed__8;
x_435 = lean_box(0);
x_436 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_434, x_435, x_8, x_9, x_10, x_11, x_433);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_437 = !lean_is_exclusive(x_436);
if (x_437 == 0)
{
return x_436;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_436, 0);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_436);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
else
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_430, 1);
lean_inc(x_441);
lean_dec(x_430);
x_396 = x_441;
goto block_429;
}
block_429:
{
lean_object* x_397; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_397 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_378, x_8, x_9, x_10, x_11, x_396);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_400 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_395, x_398, x_374, x_8, x_9, x_10, x_11, x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_403 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_402);
lean_dec(x_23);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_405 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_404);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_405, 0);
x_408 = l_Array_toList___rarg(x_407);
lean_dec(x_407);
x_409 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_408);
x_410 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_410, 0, x_386);
lean_ctor_set(x_410, 1, x_401);
lean_ctor_set(x_410, 2, x_409);
lean_ctor_set(x_405, 0, x_410);
return x_405;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_ctor_get(x_405, 0);
x_412 = lean_ctor_get(x_405, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_405);
x_413 = l_Array_toList___rarg(x_411);
lean_dec(x_411);
x_414 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_413);
x_415 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_415, 0, x_386);
lean_ctor_set(x_415, 1, x_401);
lean_ctor_set(x_415, 2, x_414);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_412);
return x_416;
}
}
else
{
uint8_t x_417; 
lean_dec(x_401);
lean_dec(x_386);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_417 = !lean_is_exclusive(x_403);
if (x_417 == 0)
{
return x_403;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_403, 0);
x_419 = lean_ctor_get(x_403, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_403);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
else
{
uint8_t x_421; 
lean_dec(x_386);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_421 = !lean_is_exclusive(x_400);
if (x_421 == 0)
{
return x_400;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_400, 0);
x_423 = lean_ctor_get(x_400, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_400);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
else
{
uint8_t x_425; 
lean_dec(x_395);
lean_dec(x_386);
lean_dec(x_374);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_425 = !lean_is_exclusive(x_397);
if (x_425 == 0)
{
return x_397;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_397, 0);
x_427 = lean_ctor_get(x_397, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_397);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
}
else
{
uint8_t x_442; 
lean_dec(x_386);
lean_dec(x_381);
lean_dec(x_378);
lean_dec(x_374);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_442 = !lean_is_exclusive(x_388);
if (x_442 == 0)
{
return x_388;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_388, 0);
x_444 = lean_ctor_get(x_388, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_388);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_378);
lean_dec(x_374);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_455 = !lean_is_exclusive(x_380);
if (x_455 == 0)
{
return x_380;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_380, 0);
x_457 = lean_ctor_get(x_380, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_380);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_484 = !lean_is_exclusive(x_373);
if (x_484 == 0)
{
return x_373;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_373, 0);
x_486 = lean_ctor_get(x_373, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_373);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_488 = !lean_is_exclusive(x_258);
if (x_488 == 0)
{
return x_258;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_258, 0);
x_490 = lean_ctor_get(x_258, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_258);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
}
else
{
uint8_t x_492; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_492 = !lean_is_exclusive(x_18);
if (x_492 == 0)
{
return x_18;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_18, 0);
x_494 = lean_ctor_get(x_18, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_18);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
else
{
uint8_t x_496; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_496 = !lean_is_exclusive(x_13);
if (x_496 == 0)
{
return x_13;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_13, 0);
x_498 = lean_ctor_get(x_13, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_13);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
}
lean_object* _init_l_Lean_Meta_rewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_rewrite___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite___lambda__1___boxed), 12, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_5);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_rewrite___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Meta_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_rewrite___lambda__1___closed__1 = _init_l_Lean_Meta_rewrite___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__1);
l_Lean_Meta_rewrite___lambda__1___closed__2 = _init_l_Lean_Meta_rewrite___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__2);
l_Lean_Meta_rewrite___lambda__1___closed__3 = _init_l_Lean_Meta_rewrite___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__3);
l_Lean_Meta_rewrite___lambda__1___closed__4 = _init_l_Lean_Meta_rewrite___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__4);
l_Lean_Meta_rewrite___lambda__1___closed__5 = _init_l_Lean_Meta_rewrite___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__5);
l_Lean_Meta_rewrite___lambda__1___closed__6 = _init_l_Lean_Meta_rewrite___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__6);
l_Lean_Meta_rewrite___lambda__1___closed__7 = _init_l_Lean_Meta_rewrite___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__7);
l_Lean_Meta_rewrite___lambda__1___closed__8 = _init_l_Lean_Meta_rewrite___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__8);
l_Lean_Meta_rewrite___lambda__1___closed__9 = _init_l_Lean_Meta_rewrite___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__9);
l_Lean_Meta_rewrite___lambda__1___closed__10 = _init_l_Lean_Meta_rewrite___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__10);
l_Lean_Meta_rewrite___lambda__1___closed__11 = _init_l_Lean_Meta_rewrite___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__11);
l_Lean_Meta_rewrite___lambda__1___closed__12 = _init_l_Lean_Meta_rewrite___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__12);
l_Lean_Meta_rewrite___lambda__1___closed__13 = _init_l_Lean_Meta_rewrite___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__13);
l_Lean_Meta_rewrite___lambda__1___closed__14 = _init_l_Lean_Meta_rewrite___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__14);
l_Lean_Meta_rewrite___lambda__1___closed__15 = _init_l_Lean_Meta_rewrite___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__15);
l_Lean_Meta_rewrite___lambda__1___closed__16 = _init_l_Lean_Meta_rewrite___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__16);
l_Lean_Meta_rewrite___lambda__1___closed__17 = _init_l_Lean_Meta_rewrite___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__17);
l_Lean_Meta_rewrite___lambda__1___closed__18 = _init_l_Lean_Meta_rewrite___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__18);
l_Lean_Meta_rewrite___lambda__1___closed__19 = _init_l_Lean_Meta_rewrite___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__19);
l_Lean_Meta_rewrite___lambda__1___closed__20 = _init_l_Lean_Meta_rewrite___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__1___closed__20);
l_Lean_Meta_rewrite___closed__1 = _init_l_Lean_Meta_rewrite___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___closed__1);
l_Lean_Meta_rewrite___closed__2 = _init_l_Lean_Meta_rewrite___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
