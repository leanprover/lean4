// Lean compiler output
// Module: Init.Lean.InductiveUtil
// Imports: Init.Lean.Environment
#include "runtime/lean.h"
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
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1;
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6;
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_reduceRecAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5;
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4;
lean_object* l_Lean_isRecStuck(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8;
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_reduceRec(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_reduceRecAux___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isRecStuck___boxed(lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_List_find___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2;
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_1__getFirstCtor(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3;
lean_object* l_Lean_reduceRec___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* lean_expr_mk_lit(lean_object*);
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7;
lean_object* l___private_Init_Lean_InductiveUtil_1__getFirstCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_free_object(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; 
lean_free_object(x_3);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_12);
x_18 = lean_box(0);
return x_18;
}
}
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___private_Init_Lean_InductiveUtil_1__getFirstCtor(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_expr_mk_const(x_10, x_6);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_12);
x_14 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_15, x_17);
x_19 = l_Array_shrink___main___rarg(x_18, x_3);
x_20 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_19, x_19, x_12, x_11);
lean_dec(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_expr_mk_const(x_21, x_6);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_23);
x_25 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_24, x_27);
lean_dec(x_24);
x_29 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_26, x_28);
x_30 = l_Array_shrink___main___rarg(x_29, x_3);
x_31 = l_Array_iterateMAux___main___at_Lean_mkApp___spec__1(x_30, x_30, x_23, x_22);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
return x_33;
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2;
x_2 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2;
x_2 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_expr_mk_lit(x_2);
x_10 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5;
x_11 = lean_expr_mk_app(x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_free_object(x_2);
lean_dec(x_4);
x_12 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8;
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_expr_mk_lit(x_18);
x_20 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5;
x_21 = lean_expr_mk_app(x_20, x_19);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_13);
x_22 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8;
return x_22;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
return x_1;
}
}
}
uint8_t l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_dec_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_find___main___rarg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_4__getRecRuleFor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_expr_has_expr_mvar(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_apply_2(x_1, x_2, x_6);
x_8 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_getAppFn___main(x_7);
x_9 = l_Lean_RecursorVal_getInduct(x_1);
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_expr_has_expr_mvar(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_7);
x_17 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_3, x_7, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_21);
x_22 = lean_apply_1(x_4, x_21);
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__2), 6, 5);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_7);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_6);
x_24 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_25);
x_27 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
lean_inc(x_7);
x_31 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_7, x_28, x_30);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_32);
x_33 = l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_7);
x_34 = l___private_Init_Lean_InductiveUtil_2__mkNullaryCtor(x_3, x_7, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_36, lean_box(0), x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_38);
x_39 = lean_apply_1(x_4, x_38);
lean_inc(x_6);
x_40 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__2), 6, 5);
lean_closure_set(x_40, 0, x_5);
lean_closure_set(x_40, 1, x_7);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_38);
lean_closure_set(x_40, 4, x_6);
x_41 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_39, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
return x_45;
}
}
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_1(x_1, x_8);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__3), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_7);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_3);
x_9 = lean_apply_1(x_3, x_7);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__4), 8, 7);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_3);
lean_closure_set(x_10, 5, x_4);
lean_closure_set(x_10, 6, x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMAux___main___at___private_Init_Lean_InductiveUtil_5__toCtorWhenK___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_InductiveUtil_5__toCtorWhenK(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Init_Lean_InductiveUtil_3__toCtorIfLit(x_8);
lean_inc(x_1);
x_10 = l___private_Init_Lean_InductiveUtil_4__getRecRuleFor(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_14);
x_16 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_9, x_17, x_19);
x_21 = l_List_lengthAux___main___rarg(x_3, x_14);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_lengthAux___main___rarg(x_23, x_14);
x_25 = lean_nat_dec_eq(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_apply_1(x_2, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_13, 2);
lean_inc(x_28);
x_29 = lean_instantiate_lparams(x_28, x_23, x_3);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 4);
lean_inc(x_31);
x_32 = lean_nat_add(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
x_35 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_34, x_4, x_14, x_29);
lean_dec(x_34);
x_36 = lean_array_get_size(x_20);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_nat_sub(x_36, x_37);
lean_dec(x_37);
x_39 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_36, x_20, x_38, x_35);
lean_dec(x_20);
lean_dec(x_36);
x_40 = lean_nat_add(x_5, x_18);
x_41 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_6, x_4, x_40, x_39);
x_42 = lean_apply_1(x_7, x_41);
return x_42;
}
}
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_7);
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_14);
x_20 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_19, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_14);
lean_inc(x_8);
x_21 = l___private_Init_Lean_InductiveUtil_5__toCtorWhenK___rarg(x_8, x_10, x_11, x_12, x_13, x_1, x_14);
x_22 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__2), 3, 2);
lean_closure_set(x_22, 0, x_8);
lean_closure_set(x_22, 1, x_14);
lean_inc(x_9);
x_23 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_21, x_22);
x_24 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_23, x_16);
return x_24;
}
}
}
lean_object* l_Lean_reduceRecAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_RecursorVal_getMajorIdx(x_6);
x_12 = lean_array_get_size(x_8);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_9, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_8, x_11);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_2);
x_18 = lean_apply_1(x_2, x_16);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg___lambda__3), 14, 13);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_7);
lean_closure_set(x_19, 3, x_8);
lean_closure_set(x_19, 4, x_11);
lean_closure_set(x_19, 5, x_12);
lean_closure_set(x_19, 6, x_10);
lean_closure_set(x_19, 7, x_1);
lean_closure_set(x_19, 8, x_17);
lean_closure_set(x_19, 9, x_2);
lean_closure_set(x_19, 10, x_3);
lean_closure_set(x_19, 11, x_4);
lean_closure_set(x_19, 12, x_5);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Lean_reduceRecAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceRecAux___rarg), 10, 0);
return x_3;
}
}
lean_object* l_Lean_reduceRecAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceRecAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_reduceRecAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceRecAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_environment_find(x_1, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_13);
x_15 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_2, x_16, x_18);
x_20 = lean_apply_3(x_4, x_12, x_7, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_3, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_3, x_23);
return x_24;
}
}
}
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_InductiveUtil_6__matchRecApp___rarg), 4, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_InductiveUtil_6__matchRecApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_InductiveUtil_6__matchRecApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_reduceRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_6);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = lean_environment_find(x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_17);
x_19 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_6, x_20, x_22);
x_24 = l_Lean_reduceRecAux___rarg(x_1, x_2, x_3, x_4, x_5, x_16, x_11, x_23, x_7, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_7, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_7, x_27);
return x_28;
}
}
}
lean_object* l_Lean_reduceRec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceRec___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_reduceRec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceRec(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_isRecStuck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_environment_find(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_16);
x_18 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_19, x_21);
x_23 = l_Lean_RecursorVal_getMajorIdx(x_14);
lean_dec(x_14);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_array_fget(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_1(x_2, x_30);
x_33 = lean_apply_4(x_31, lean_box(0), lean_box(0), x_32, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_apply_2(x_35, lean_box(0), x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = lean_apply_2(x_39, lean_box(0), x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
return x_45;
}
}
}
lean_object* l_Lean_isRecStuck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isRecStuck___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_isRecStuck___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isRecStuck(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_InductiveUtil(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__1);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__2);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__3);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__4);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__5);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__6);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__7);
l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8 = _init_l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8();
lean_mark_persistent(l___private_Init_Lean_InductiveUtil_3__toCtorIfLit___closed__8);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
