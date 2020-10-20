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
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__9;
lean_object* l_Lean_Meta_rewrite___lambda__3___closed__3;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__8;
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___closed__1;
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__5;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__2___closed__1;
lean_object* l_Lean_Meta_rewrite___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___closed__2;
lean_object* l_Lean_Meta_rewrite___lambda__2___closed__4;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__2(lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__3___closed__2;
lean_object* l_Lean_Meta_rewrite___lambda__3___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewrite___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l_Lean_Meta_rewrite___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_rewrite___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__2___closed__3;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__1(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__7;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__2___closed__5;
lean_object* l_Lean_Meta_rewrite_match__3(lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l_Lean_Meta_rewrite___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__4(lean_object*);
lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__3;
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__6;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__2___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_rewrite___lambda__4___closed__10;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_rewrite___spec__3(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_rewrite_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_rewrite_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Meta_rewrite_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_rewrite_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_rewrite_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_rewrite_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_rewrite_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_rewrite_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_rewrite_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_34; 
x_34 = l_Lean_Expr_isFVar(x_2);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 0;
x_9 = x_35;
goto block_33;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Occurrences_beq(x_3, x_36);
x_9 = x_37;
goto block_33;
}
block_33:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_17 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_10, x_12, x_1, x_11, x_15, x_4, x_5, x_6, x_7, x_16);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = l_Lean_mkOptionalNode___closed__2;
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_expr_abstract(x_1, x_30);
lean_dec(x_30);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewrite___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_2, x_16, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_postprocessAppMVars(x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_6, x_23, x_23, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_Array_toList___rarg(x_26);
lean_dec(x_26);
x_28 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_33 = l_List_map___main___at_Lean_Meta_rewrite___spec__3(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive is not type correct");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__2___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_expr_instantiate1(x_1, x_2);
x_17 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_16, x_11, x_12, x_13, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_n(x_3, 2);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_3, x_3, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_appFn_x21(x_21);
lean_dec(x_21);
x_24 = l_Lean_mkApp(x_23, x_1);
x_25 = l_Lean_Meta_rewrite___lambda__2___closed__2;
x_26 = 0;
x_27 = l_Lean_mkLambda(x_25, x_26, x_4, x_24);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_28 = l_Lean_Meta_isTypeCorrect(x_27, x_11, x_12, x_13, x_14, x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Meta_rewrite___lambda__2___closed__5;
x_33 = lean_box(0);
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_7, x_32, x_33, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_rewrite___lambda__1(x_3, x_27, x_5, x_6, x_7, x_8, x_9, x_18, x_40, x_11, x_12, x_13, x_14, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find instance of the pattern in the target expression");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_1, x_12, x_13, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_18);
x_20 = l_Lean_Meta_kabstract___at_Lean_Meta_rewrite___spec__1(x_18, x_2, x_3, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_hasLooseBVars(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = l_Lean_Meta_rewrite___lambda__3___closed__3;
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_24, x_25, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_Meta_rewrite___lambda__2(x_21, x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_31, x_12, x_13, x_14, x_15, x_22);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality of iff proof expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern is a metavariable");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nfrom equation");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewrite___lambda__4___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propext");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__4___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___lambda__4___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewrite___lambda__4___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 1;
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_14, x_17, x_16, x_18, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_23, x_23, x_26, x_1);
x_28 = l_Lean_Expr_iff_x3f___closed__2;
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_Lean_Expr_isAppOfArity___main(x_25, x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Expr_eq_x3f___closed__2;
x_32 = lean_unsigned_to_nat(3u);
x_33 = l_Lean_Expr_isAppOfArity___main(x_25, x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_34 = l_Lean_Meta_rewrite___lambda__4___closed__3;
x_35 = lean_box(0);
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_34, x_35, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Lean_Expr_appFn_x21(x_25);
x_38 = l_Lean_Expr_appFn_x21(x_37);
x_39 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_40 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
x_41 = l_Lean_Expr_appArg_x21(x_25);
if (x_4 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Expr_getAppFn___main(x_40);
x_43 = l_Lean_Expr_isMVar(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_rewrite___lambda__3(x_5, x_40, x_6, x_41, x_39, x_27, x_2, x_3, x_23, x_24, x_44, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_24);
lean_dec(x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_46 = l_Lean_indentExpr(x_40);
x_47 = l_Lean_Meta_rewrite___lambda__4___closed__5;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_rewrite___lambda__4___closed__7;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_indentExpr(x_25);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_54, x_55, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_61 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_27, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_40);
lean_inc(x_41);
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_41, x_40, x_8, x_9, x_10, x_11, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_getAppFn___main(x_41);
x_68 = l_Lean_Expr_isMVar(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_69 = lean_box(0);
x_70 = l_Lean_Meta_rewrite___lambda__3(x_5, x_41, x_6, x_40, x_39, x_62, x_2, x_3, x_23, x_24, x_69, x_8, x_9, x_10, x_11, x_66);
lean_dec(x_24);
lean_dec(x_40);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_62);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_71 = l_Lean_indentExpr(x_41);
x_72 = l_Lean_Meta_rewrite___lambda__4___closed__5;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_rewrite___lambda__4___closed__7;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_indentExpr(x_65);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_box(0);
x_81 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_79, x_80, x_8, x_9, x_10, x_11, x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_62);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_64);
if (x_86 == 0)
{
return x_64;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_64, 0);
x_88 = lean_ctor_get(x_64, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_64);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_61);
if (x_90 == 0)
{
return x_61;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_61, 0);
x_92 = lean_ctor_get(x_61, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_61);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = l_Lean_Expr_appFn_x21(x_25);
x_95 = l_Lean_Expr_appArg_x21(x_94);
lean_dec(x_94);
x_96 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_96);
lean_inc(x_95);
x_97 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_95, x_96, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Meta_rewrite___lambda__4___closed__10;
x_101 = l_Lean_mkApp3(x_100, x_95, x_96, x_27);
x_102 = l_Lean_Expr_eq_x3f___closed__2;
x_103 = lean_unsigned_to_nat(3u);
x_104 = l_Lean_Expr_isAppOfArity___main(x_98, x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_105 = l_Lean_Meta_rewrite___lambda__4___closed__3;
x_106 = lean_box(0);
x_107 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_105, x_106, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = l_Lean_Expr_appFn_x21(x_98);
x_109 = l_Lean_Expr_appFn_x21(x_108);
x_110 = l_Lean_Expr_appArg_x21(x_109);
lean_dec(x_109);
x_111 = l_Lean_Expr_appArg_x21(x_108);
lean_dec(x_108);
x_112 = l_Lean_Expr_appArg_x21(x_98);
if (x_4 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Lean_Expr_getAppFn___main(x_111);
x_114 = l_Lean_Expr_isMVar(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_98);
x_115 = lean_box(0);
x_116 = l_Lean_Meta_rewrite___lambda__3(x_5, x_111, x_6, x_112, x_110, x_101, x_2, x_3, x_23, x_24, x_115, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_24);
lean_dec(x_112);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_101);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_117 = l_Lean_indentExpr(x_111);
x_118 = l_Lean_Meta_rewrite___lambda__4___closed__5;
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Meta_rewrite___lambda__4___closed__7;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_indentExpr(x_98);
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_box(0);
x_127 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_125, x_126, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; 
lean_dec(x_98);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_132 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_101, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_111);
lean_inc(x_112);
x_135 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_112, x_111, x_8, x_9, x_10, x_11, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Expr_getAppFn___main(x_112);
x_139 = l_Lean_Expr_isMVar(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_136);
x_140 = lean_box(0);
x_141 = l_Lean_Meta_rewrite___lambda__3(x_5, x_112, x_6, x_111, x_110, x_133, x_2, x_3, x_23, x_24, x_140, x_8, x_9, x_10, x_11, x_137);
lean_dec(x_24);
lean_dec(x_111);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_133);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_142 = l_Lean_indentExpr(x_112);
x_143 = l_Lean_Meta_rewrite___lambda__4___closed__5;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Meta_rewrite___lambda__4___closed__7;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_indentExpr(x_136);
x_148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_box(0);
x_152 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_150, x_151, x_8, x_9, x_10, x_11, x_137);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_152);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_133);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_135);
if (x_157 == 0)
{
return x_135;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_135, 0);
x_159 = lean_ctor_get(x_135, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_135);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_132);
if (x_161 == 0)
{
return x_132;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_132, 0);
x_163 = lean_ctor_get(x_132, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_132);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_97);
if (x_165 == 0)
{
return x_97;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_97, 0);
x_167 = lean_ctor_get(x_97, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_97);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_19);
if (x_169 == 0)
{
return x_19;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_19, 0);
x_171 = lean_ctor_get(x_19, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_19);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_13);
if (x_173 == 0)
{
return x_13;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_13, 0);
x_175 = lean_ctor_get(x_13, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_13);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
static lean_object* _init_l_Lean_Meta_rewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_rewrite___closed__2() {
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
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_rewrite___lambda__4___boxed), 12, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_5);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__5___spec__2___rarg), 7, 2);
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
lean_object* l_Lean_Meta_rewrite___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_rewrite___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_rewrite___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_rewrite___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
lean_object* l_Lean_Meta_rewrite___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_rewrite___lambda__4(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
l_Lean_Meta_rewrite___lambda__2___closed__1 = _init_l_Lean_Meta_rewrite___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__2___closed__1);
l_Lean_Meta_rewrite___lambda__2___closed__2 = _init_l_Lean_Meta_rewrite___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__2___closed__2);
l_Lean_Meta_rewrite___lambda__2___closed__3 = _init_l_Lean_Meta_rewrite___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__2___closed__3);
l_Lean_Meta_rewrite___lambda__2___closed__4 = _init_l_Lean_Meta_rewrite___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__2___closed__4);
l_Lean_Meta_rewrite___lambda__2___closed__5 = _init_l_Lean_Meta_rewrite___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__2___closed__5);
l_Lean_Meta_rewrite___lambda__3___closed__1 = _init_l_Lean_Meta_rewrite___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__3___closed__1);
l_Lean_Meta_rewrite___lambda__3___closed__2 = _init_l_Lean_Meta_rewrite___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__3___closed__2);
l_Lean_Meta_rewrite___lambda__3___closed__3 = _init_l_Lean_Meta_rewrite___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__3___closed__3);
l_Lean_Meta_rewrite___lambda__4___closed__1 = _init_l_Lean_Meta_rewrite___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__1);
l_Lean_Meta_rewrite___lambda__4___closed__2 = _init_l_Lean_Meta_rewrite___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__2);
l_Lean_Meta_rewrite___lambda__4___closed__3 = _init_l_Lean_Meta_rewrite___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__3);
l_Lean_Meta_rewrite___lambda__4___closed__4 = _init_l_Lean_Meta_rewrite___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__4);
l_Lean_Meta_rewrite___lambda__4___closed__5 = _init_l_Lean_Meta_rewrite___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__5);
l_Lean_Meta_rewrite___lambda__4___closed__6 = _init_l_Lean_Meta_rewrite___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__6);
l_Lean_Meta_rewrite___lambda__4___closed__7 = _init_l_Lean_Meta_rewrite___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__7);
l_Lean_Meta_rewrite___lambda__4___closed__8 = _init_l_Lean_Meta_rewrite___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__8);
l_Lean_Meta_rewrite___lambda__4___closed__9 = _init_l_Lean_Meta_rewrite___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__9);
l_Lean_Meta_rewrite___lambda__4___closed__10 = _init_l_Lean_Meta_rewrite___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Meta_rewrite___lambda__4___closed__10);
l_Lean_Meta_rewrite___closed__1 = _init_l_Lean_Meta_rewrite___closed__1();
lean_mark_persistent(l_Lean_Meta_rewrite___closed__1);
l_Lean_Meta_rewrite___closed__2 = _init_l_Lean_Meta_rewrite___closed__2();
lean_mark_persistent(l_Lean_Meta_rewrite___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
