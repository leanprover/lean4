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
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__11;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__17;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__4;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
extern lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__16;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Meta_isEtaUnassignedMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___closed__2;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__13;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__14;
lean_object* l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewriteCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__10;
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_rewriteCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewriteCore___lambda__1___closed__12;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Expr_toHeadIndex___main(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_st_mk_ref(x_12, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_9, x_11, x_1, x_10, x_14, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
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
else
{
uint8_t x_24; 
lean_dec(x_14);
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
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_rewriteCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_31 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Meta_isEtaUnassignedMVar___spec__1(x_30, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(lean_object* x_1) {
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
x_7 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_5);
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
x_11 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_rewriteCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality of iff proof expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive is not type correct");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find instance of the pattern in the target expression");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern is a metavariable");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_rewriteCore___lambda__1___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propext");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___lambda__1___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
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
x_33 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
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
lean_dec(x_24);
if (x_4 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Expr_getAppFn___main(x_39);
x_42 = l_Lean_Expr_isMVar(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
x_46 = l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(x_44, x_39, x_6, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_117; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_117 = l_Lean_Expr_hasLooseBVars(x_47);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_118 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_119 = lean_box(0);
x_120 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_118, x_119, x_8, x_9, x_10, x_11, x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
else
{
x_49 = x_48;
goto block_116;
}
block_116:
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_96; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Expr_appFn_x21(x_55);
lean_dec(x_55);
x_58 = l_Lean_mkApp(x_57, x_47);
x_59 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_60 = 0;
x_61 = l_Lean_mkLambda(x_59, x_60, x_38, x_58);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_61);
x_96 = l_Lean_Meta_isTypeCorrect(x_61, x_8, x_9, x_10, x_11, x_56);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
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
x_100 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
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
}
else
{
uint8_t x_108; 
lean_dec(x_61);
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_96);
if (x_108 == 0)
{
return x_96;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_96, 0);
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_96);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
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
x_71 = l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_70);
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
x_75 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_74);
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
x_80 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_79);
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
uint8_t x_112; 
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
x_112 = !lean_is_exclusive(x_54);
if (x_112 == 0)
{
return x_54;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_54, 0);
x_114 = lean_ctor_get(x_54, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_54);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
uint8_t x_125; 
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
x_125 = !lean_is_exclusive(x_46);
if (x_125 == 0)
{
return x_46;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_46, 0);
x_127 = lean_ctor_get(x_46, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_129 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_130 = lean_box(0);
x_131 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_129, x_130, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_136 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_26, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_227; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_40);
x_227 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_40, x_39, x_8, x_9, x_10, x_11, x_138);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Lean_Expr_getAppFn___main(x_40);
x_230 = l_Lean_Expr_isMVar(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
x_139 = x_228;
goto block_226;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_137);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_231 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_232 = lean_box(0);
x_233 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_231, x_232, x_8, x_9, x_10, x_11, x_228);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
return x_233;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_233);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_137);
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
x_238 = !lean_is_exclusive(x_227);
if (x_238 == 0)
{
return x_227;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_227, 0);
x_240 = lean_ctor_get(x_227, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_227);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
block_226:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_141);
x_143 = l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(x_141, x_40, x_6, x_8, x_9, x_10, x_11, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_214; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_214 = l_Lean_Expr_hasLooseBVars(x_144);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
x_215 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_216 = lean_box(0);
x_217 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_215, x_216, x_8, x_9, x_10, x_11, x_145);
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
x_146 = x_145;
goto block_213;
}
block_213:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_expr_instantiate1(x_144, x_39);
lean_dec(x_39);
x_148 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_147, x_8, x_9, x_10, x_11, x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_141, 2);
x_151 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_141, x_141, x_8, x_9, x_10, x_11, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_193; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_Expr_appFn_x21(x_152);
lean_dec(x_152);
x_155 = l_Lean_mkApp(x_154, x_144);
x_156 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_157 = 0;
x_158 = l_Lean_mkLambda(x_156, x_157, x_38, x_155);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_158);
x_193 = l_Lean_Meta_isTypeCorrect(x_158, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_158);
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_23);
lean_dec(x_22);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_198 = lean_box(0);
x_199 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_197, x_198, x_8, x_9, x_10, x_11, x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_193, 1);
lean_inc(x_204);
lean_dec(x_193);
x_159 = x_204;
goto block_192;
}
}
else
{
uint8_t x_205; 
lean_dec(x_158);
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_193);
if (x_205 == 0)
{
return x_193;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_193, 0);
x_207 = lean_ctor_get(x_193, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_193);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
block_192:
{
lean_object* x_160; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_160 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_141, x_8, x_9, x_10, x_11, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_163 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_158, x_161, x_137, x_8, x_9, x_10, x_11, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_166 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_165);
lean_dec(x_23);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_167);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = l_Array_toList___rarg(x_170);
lean_dec(x_170);
x_172 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_171);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_149);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_168, 0, x_173);
return x_168;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_168, 0);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_168);
x_176 = l_Array_toList___rarg(x_174);
lean_dec(x_174);
x_177 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_176);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_149);
lean_ctor_set(x_178, 1, x_164);
lean_ctor_set(x_178, 2, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
}
else
{
uint8_t x_180; 
lean_dec(x_164);
lean_dec(x_149);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_180 = !lean_is_exclusive(x_166);
if (x_180 == 0)
{
return x_166;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_166, 0);
x_182 = lean_ctor_get(x_166, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_166);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_149);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_163);
if (x_184 == 0)
{
return x_163;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_163, 0);
x_186 = lean_ctor_get(x_163, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_163);
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
lean_dec(x_158);
lean_dec(x_149);
lean_dec(x_137);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_160);
if (x_188 == 0)
{
return x_160;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_160, 0);
x_190 = lean_ctor_get(x_160, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_160);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_149);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_137);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_209 = !lean_is_exclusive(x_151);
if (x_209 == 0)
{
return x_151;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_151, 0);
x_211 = lean_ctor_get(x_151, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_151);
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
lean_dec(x_141);
lean_dec(x_137);
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
x_222 = !lean_is_exclusive(x_143);
if (x_222 == 0)
{
return x_143;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_143, 0);
x_224 = lean_ctor_get(x_143, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_143);
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
uint8_t x_242; 
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
x_242 = !lean_is_exclusive(x_136);
if (x_242 == 0)
{
return x_136;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_136, 0);
x_244 = lean_ctor_get(x_136, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_136);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = l_Lean_Expr_appFn_x21(x_24);
x_247 = l_Lean_Expr_appArg_x21(x_246);
lean_dec(x_246);
x_248 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_248);
lean_inc(x_247);
x_249 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_247, x_248, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_Meta_rewriteCore___lambda__1___closed__17;
x_253 = l_Lean_mkApp3(x_252, x_247, x_248, x_26);
x_254 = l_Lean_Expr_eq_x3f___closed__2;
x_255 = lean_unsigned_to_nat(3u);
x_256 = l_Lean_Expr_isAppOfArity___main(x_250, x_254, x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_257 = l_Lean_Meta_rewriteCore___lambda__1___closed__3;
x_258 = lean_box(0);
x_259 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_257, x_258, x_8, x_9, x_10, x_11, x_251);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = l_Lean_Expr_appFn_x21(x_250);
x_261 = l_Lean_Expr_appFn_x21(x_260);
x_262 = l_Lean_Expr_appArg_x21(x_261);
lean_dec(x_261);
x_263 = l_Lean_Expr_appArg_x21(x_260);
lean_dec(x_260);
x_264 = l_Lean_Expr_appArg_x21(x_250);
lean_dec(x_250);
if (x_4 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = l_Lean_Expr_getAppFn___main(x_263);
x_266 = l_Lean_Expr_isMVar(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_251);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_268);
x_270 = l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(x_268, x_263, x_6, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_341; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_341 = l_Lean_Expr_hasLooseBVars(x_271);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_dec(x_271);
lean_dec(x_268);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
x_342 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_343 = lean_box(0);
x_344 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_342, x_343, x_8, x_9, x_10, x_11, x_272);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_345 = !lean_is_exclusive(x_344);
if (x_345 == 0)
{
return x_344;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_344, 0);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_344);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
else
{
x_273 = x_272;
goto block_340;
}
block_340:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_expr_instantiate1(x_271, x_264);
lean_dec(x_264);
x_275 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_274, x_8, x_9, x_10, x_11, x_273);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_268, 2);
x_278 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_268, x_268, x_8, x_9, x_10, x_11, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_320; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = l_Lean_Expr_appFn_x21(x_279);
lean_dec(x_279);
x_282 = l_Lean_mkApp(x_281, x_271);
x_283 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_284 = 0;
x_285 = l_Lean_mkLambda(x_283, x_284, x_262, x_282);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_285);
x_320 = l_Lean_Meta_isTypeCorrect(x_285, x_8, x_9, x_10, x_11, x_280);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_unbox(x_321);
lean_dec(x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
lean_dec(x_285);
lean_dec(x_276);
lean_dec(x_268);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_325 = lean_box(0);
x_326 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_324, x_325, x_8, x_9, x_10, x_11, x_323);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
return x_326;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_326, 0);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_326);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
else
{
lean_object* x_331; 
x_331 = lean_ctor_get(x_320, 1);
lean_inc(x_331);
lean_dec(x_320);
x_286 = x_331;
goto block_319;
}
}
else
{
uint8_t x_332; 
lean_dec(x_285);
lean_dec(x_276);
lean_dec(x_268);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_332 = !lean_is_exclusive(x_320);
if (x_332 == 0)
{
return x_320;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_320, 0);
x_334 = lean_ctor_get(x_320, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_320);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
block_319:
{
lean_object* x_287; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_287 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_268, x_8, x_9, x_10, x_11, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_290 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_285, x_288, x_253, x_8, x_9, x_10, x_11, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_293 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_292);
lean_dec(x_23);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
x_295 = l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_294);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_295, 0);
x_298 = l_Array_toList___rarg(x_297);
lean_dec(x_297);
x_299 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_298);
x_300 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_300, 0, x_276);
lean_ctor_set(x_300, 1, x_291);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_295, 0, x_300);
return x_295;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_ctor_get(x_295, 0);
x_302 = lean_ctor_get(x_295, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_295);
x_303 = l_Array_toList___rarg(x_301);
lean_dec(x_301);
x_304 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_303);
x_305 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_305, 0, x_276);
lean_ctor_set(x_305, 1, x_291);
lean_ctor_set(x_305, 2, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_302);
return x_306;
}
}
else
{
uint8_t x_307; 
lean_dec(x_291);
lean_dec(x_276);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_307 = !lean_is_exclusive(x_293);
if (x_307 == 0)
{
return x_293;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_293, 0);
x_309 = lean_ctor_get(x_293, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_293);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_276);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_311 = !lean_is_exclusive(x_290);
if (x_311 == 0)
{
return x_290;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_290, 0);
x_313 = lean_ctor_get(x_290, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_290);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_285);
lean_dec(x_276);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_315 = !lean_is_exclusive(x_287);
if (x_315 == 0)
{
return x_287;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_276);
lean_dec(x_271);
lean_dec(x_268);
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_336 = !lean_is_exclusive(x_278);
if (x_336 == 0)
{
return x_278;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_278, 0);
x_338 = lean_ctor_get(x_278, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_278);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_268);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_349 = !lean_is_exclusive(x_270);
if (x_349 == 0)
{
return x_270;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_270, 0);
x_351 = lean_ctor_get(x_270, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_270);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_253);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_353 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_354 = lean_box(0);
x_355 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_353, x_354, x_8, x_9, x_10, x_11, x_251);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
return x_355;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_355, 0);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_355);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
lean_object* x_360; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_360 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_253, x_8, x_9, x_10, x_11, x_251);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_451; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_263);
lean_inc(x_264);
x_451 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_264, x_263, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = l_Lean_Expr_getAppFn___main(x_264);
x_454 = l_Lean_Expr_isMVar(x_453);
lean_dec(x_453);
if (x_454 == 0)
{
x_363 = x_452;
goto block_450;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
lean_dec(x_361);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_5);
x_455 = l_Lean_Meta_rewriteCore___lambda__1___closed__14;
x_456 = lean_box(0);
x_457 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_455, x_456, x_8, x_9, x_10, x_11, x_452);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
return x_457;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_457);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_361);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_462 = !lean_is_exclusive(x_451);
if (x_462 == 0)
{
return x_451;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_451, 0);
x_464 = lean_ctor_get(x_451, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_451);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
block_450:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_5, x_8, x_9, x_10, x_11, x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_365);
x_367 = l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(x_365, x_264, x_6, x_8, x_9, x_10, x_11, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_438; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_438 = l_Lean_Expr_hasLooseBVars(x_368);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_368);
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
x_439 = l_Lean_Meta_rewriteCore___lambda__1___closed__11;
x_440 = lean_box(0);
x_441 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_439, x_440, x_8, x_9, x_10, x_11, x_369);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
return x_441;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_441, 0);
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_441);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
else
{
x_370 = x_369;
goto block_437;
}
block_437:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_expr_instantiate1(x_368, x_263);
lean_dec(x_263);
x_372 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_371, x_8, x_9, x_10, x_11, x_370);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_n(x_365, 2);
x_375 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_365, x_365, x_8, x_9, x_10, x_11, x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_417; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = l_Lean_Expr_appFn_x21(x_376);
lean_dec(x_376);
x_379 = l_Lean_mkApp(x_378, x_368);
x_380 = l_Lean_Meta_rewriteCore___lambda__1___closed__5;
x_381 = 0;
x_382 = l_Lean_mkLambda(x_380, x_381, x_262, x_379);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_382);
x_417 = l_Lean_Meta_isTypeCorrect(x_382, x_8, x_9, x_10, x_11, x_377);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_unbox(x_418);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
lean_dec(x_382);
lean_dec(x_373);
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_23);
lean_dec(x_22);
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_420);
lean_dec(x_417);
x_421 = l_Lean_Meta_rewriteCore___lambda__1___closed__8;
x_422 = lean_box(0);
x_423 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_3, x_421, x_422, x_8, x_9, x_10, x_11, x_420);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
return x_423;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_423, 0);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_423);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
else
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_417, 1);
lean_inc(x_428);
lean_dec(x_417);
x_383 = x_428;
goto block_416;
}
}
else
{
uint8_t x_429; 
lean_dec(x_382);
lean_dec(x_373);
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_429 = !lean_is_exclusive(x_417);
if (x_429 == 0)
{
return x_417;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_417, 0);
x_431 = lean_ctor_get(x_417, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_417);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
block_416:
{
lean_object* x_384; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_384 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_365, x_8, x_9, x_10, x_11, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_387 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_382, x_385, x_361, x_8, x_9, x_10, x_11, x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_390 = l_Lean_Meta_postprocessAppMVars(x_2, x_3, x_22, x_23, x_8, x_9, x_10, x_11, x_389);
lean_dec(x_23);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(x_22, x_25, x_25, x_8, x_9, x_10, x_11, x_391);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = l_Array_toList___rarg(x_394);
lean_dec(x_394);
x_396 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_395);
x_397 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_397, 0, x_373);
lean_ctor_set(x_397, 1, x_388);
lean_ctor_set(x_397, 2, x_396);
lean_ctor_set(x_392, 0, x_397);
return x_392;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_398 = lean_ctor_get(x_392, 0);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_392);
x_400 = l_Array_toList___rarg(x_398);
lean_dec(x_398);
x_401 = l_List_map___main___at_Lean_Meta_rewriteCore___spec__4(x_400);
x_402 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_402, 0, x_373);
lean_ctor_set(x_402, 1, x_388);
lean_ctor_set(x_402, 2, x_401);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_399);
return x_403;
}
}
else
{
uint8_t x_404; 
lean_dec(x_388);
lean_dec(x_373);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_404 = !lean_is_exclusive(x_390);
if (x_404 == 0)
{
return x_390;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_390, 0);
x_406 = lean_ctor_get(x_390, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_390);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_373);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_408 = !lean_is_exclusive(x_387);
if (x_408 == 0)
{
return x_387;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_387, 0);
x_410 = lean_ctor_get(x_387, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_387);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_382);
lean_dec(x_373);
lean_dec(x_361);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_412 = !lean_is_exclusive(x_384);
if (x_412 == 0)
{
return x_384;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_384, 0);
x_414 = lean_ctor_get(x_384, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_384);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_373);
lean_dec(x_368);
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_433 = !lean_is_exclusive(x_375);
if (x_433 == 0)
{
return x_375;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_375, 0);
x_435 = lean_ctor_get(x_375, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_375);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_365);
lean_dec(x_361);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_446 = !lean_is_exclusive(x_367);
if (x_446 == 0)
{
return x_367;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_367, 0);
x_448 = lean_ctor_get(x_367, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_367);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_466 = !lean_is_exclusive(x_360);
if (x_466 == 0)
{
return x_360;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_360, 0);
x_468 = lean_ctor_get(x_360, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_360);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_248);
lean_dec(x_247);
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
x_470 = !lean_is_exclusive(x_249);
if (x_470 == 0)
{
return x_249;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_249, 0);
x_472 = lean_ctor_get(x_249, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_249);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_474 = !lean_is_exclusive(x_18);
if (x_474 == 0)
{
return x_18;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_18, 0);
x_476 = lean_ctor_get(x_18, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_18);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_478 = !lean_is_exclusive(x_13);
if (x_478 == 0)
{
return x_13;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_13, 0);
x_480 = lean_ctor_get(x_13, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_13);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_rewriteCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_rewriteCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_rewriteCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_rewriteCore___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_rewriteCore___lambda__1___boxed), 12, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_5);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 4);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract___at_Lean_Meta_rewriteCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMAux___main___at_Lean_Meta_rewriteCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Meta_rewriteCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_rewriteCore___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_Meta_rewriteCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_rewriteCore(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l_Lean_Meta_rewriteCore___lambda__1___closed__1 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__1);
l_Lean_Meta_rewriteCore___lambda__1___closed__2 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__2);
l_Lean_Meta_rewriteCore___lambda__1___closed__3 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__3);
l_Lean_Meta_rewriteCore___lambda__1___closed__4 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__4);
l_Lean_Meta_rewriteCore___lambda__1___closed__5 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__5);
l_Lean_Meta_rewriteCore___lambda__1___closed__6 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__6);
l_Lean_Meta_rewriteCore___lambda__1___closed__7 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__7);
l_Lean_Meta_rewriteCore___lambda__1___closed__8 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__8);
l_Lean_Meta_rewriteCore___lambda__1___closed__9 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__9);
l_Lean_Meta_rewriteCore___lambda__1___closed__10 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__10);
l_Lean_Meta_rewriteCore___lambda__1___closed__11 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__11);
l_Lean_Meta_rewriteCore___lambda__1___closed__12 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__12);
l_Lean_Meta_rewriteCore___lambda__1___closed__13 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__13);
l_Lean_Meta_rewriteCore___lambda__1___closed__14 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__14);
l_Lean_Meta_rewriteCore___lambda__1___closed__15 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__15);
l_Lean_Meta_rewriteCore___lambda__1___closed__16 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__16);
l_Lean_Meta_rewriteCore___lambda__1___closed__17 = _init_l_Lean_Meta_rewriteCore___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_rewriteCore___lambda__1___closed__17);
l_Lean_Meta_rewriteCore___closed__1 = _init_l_Lean_Meta_rewriteCore___closed__1();
lean_mark_persistent(l_Lean_Meta_rewriteCore___closed__1);
l_Lean_Meta_rewriteCore___closed__2 = _init_l_Lean_Meta_rewriteCore___closed__2();
lean_mark_persistent(l_Lean_Meta_rewriteCore___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
