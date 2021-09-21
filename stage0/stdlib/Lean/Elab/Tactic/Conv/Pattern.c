// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Pattern
// Imports: Init Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Conv.Basic
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
extern lean_object* l_Std_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrLemmas___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__8;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__11;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7;
lean_object* l_Lean_Meta_applyRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2;
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5;
lean_object* l_Lean_Elab_Term_withoutPending___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___closed__10;
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 9);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 4, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 5, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 6, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 7, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 8, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2;
x_2 = l_Std_PersistentHashMap_empty___at_Lean_KeyedDeclsAttribute_ExtensionState_declNames___default___spec__1;
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_getCongrLemmas___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1;
x_8 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1;
x_15 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = 2;
lean_ctor_set_uint8(x_11, 5, x_17);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_19 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_3, x_18, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
lean_inc(x_9);
x_33 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_3, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_st_ref_get(x_9, x_35);
lean_dec(x_9);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_38);
x_41 = lean_st_ref_set(x_2, x_38, x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_33);
if (x_50 == 0)
{
return x_33;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_33, 0);
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_33);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_54 = lean_ctor_get_uint8(x_11, 0);
x_55 = lean_ctor_get_uint8(x_11, 1);
x_56 = lean_ctor_get_uint8(x_11, 2);
x_57 = lean_ctor_get_uint8(x_11, 3);
x_58 = lean_ctor_get_uint8(x_11, 4);
x_59 = lean_ctor_get_uint8(x_11, 6);
x_60 = lean_ctor_get_uint8(x_11, 7);
x_61 = lean_ctor_get_uint8(x_11, 8);
x_62 = lean_ctor_get_uint8(x_11, 9);
x_63 = lean_ctor_get_uint8(x_11, 10);
x_64 = lean_ctor_get_uint8(x_11, 11);
x_65 = lean_ctor_get_uint8(x_11, 12);
lean_dec(x_11);
x_66 = 2;
x_67 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_67, 0, x_54);
lean_ctor_set_uint8(x_67, 1, x_55);
lean_ctor_set_uint8(x_67, 2, x_56);
lean_ctor_set_uint8(x_67, 3, x_57);
lean_ctor_set_uint8(x_67, 4, x_58);
lean_ctor_set_uint8(x_67, 5, x_66);
lean_ctor_set_uint8(x_67, 6, x_59);
lean_ctor_set_uint8(x_67, 7, x_60);
lean_ctor_set_uint8(x_67, 8, x_61);
lean_ctor_set_uint8(x_67, 9, x_62);
lean_ctor_set_uint8(x_67, 10, x_63);
lean_ctor_set_uint8(x_67, 11, x_64);
lean_ctor_set_uint8(x_67, 12, x_65);
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_12);
lean_ctor_set(x_68, 2, x_13);
lean_ctor_set(x_68, 3, x_14);
lean_ctor_set(x_68, 4, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_69 = l_Lean_Meta_isExprDefEqGuarded(x_1, x_3, x_68, x_7, x_8, x_9, x_10);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec(x_69);
lean_inc(x_9);
x_79 = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(x_3, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_st_ref_get(x_9, x_81);
lean_dec(x_9);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
lean_inc(x_84);
x_87 = lean_st_ref_set(x_2, x_84, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_84);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_9);
x_93 = lean_ctor_get(x_79, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_95 = x_79;
} else {
 lean_dec_ref(x_79);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2___boxed), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_box(0);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_IO_mkRef___rarg(x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed), 10, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_12);
x_18 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1;
x_19 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_inc(x_6);
x_21 = l_Lean_Meta_Simp_main(x_2, x_15, x_20, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_6, x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_12, x_25);
lean_dec(x_12);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_22);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
lean_ctor_set(x_26, 0, x_8);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_27, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
x_39 = l_Lean_Expr_mvarId_x21(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_22);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_26, 0, x_41);
return x_26;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_ctor_get(x_27, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_44 = x_27;
} else {
 lean_dec_ref(x_27);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Expr_mvarId_x21(x_43);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_22);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'pattern' conv tactic failed, pattern was not found");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_withoutPending___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Tactic_Conv_getLhs(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_17 = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f(x_12, x_15, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_indentExpr(x_12);
x_21 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_30 = l_Lean_Meta_Simp_Result_getProof(x_29, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_Conv_updateLhs(x_33, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Lean_Meta_applyRefl(x_37, x_39, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Tactic_replaceMainGoal(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
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
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
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
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
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
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_30);
if (x_57 == 0)
{
return x_30;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_30, 0);
x_59 = lean_ctor_get(x_30, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_30);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
return x_17;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_14);
if (x_65 == 0)
{
return x_14;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_14, 0);
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Conv");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__8;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__10;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__11;
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_box(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_17);
lean_closure_set(x_21, 2, x_19);
lean_closure_set(x_21, 3, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1), 10, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Tactic_withMainContext___rarg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
x_2 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalPattern");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalPattern), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_Conv_evalPattern___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Pattern(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__1);
l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__2);
l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3 = _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___rarg___closed__3);
l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1 = _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__1);
l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2 = _init_l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_findPattern_x3f___closed__2);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__1);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__2);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__3);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__4);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__5);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__6);
l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___lambda__1___closed__7);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__1 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__2 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__3 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__4 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__5 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__5);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__6 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__7 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__7);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__8 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__8);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__9 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__9);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__10 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__10);
l_Lean_Elab_Tactic_Conv_evalPattern___closed__11 = _init_l_Lean_Elab_Tactic_Conv_evalPattern___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Conv_evalPattern___closed__11);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
