// Lean compiler output
// Module: Init.Lean.QuotUtil
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_1__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isQuotRecStuck(lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_isQuotRecStuck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRec___boxed(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_reduceQuotRecAux(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_environment_find(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_20 = lean_box(x_19);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_21 = l_Lean_exprIsInhabited;
x_22 = lean_array_get(x_21, x_3, x_4);
x_23 = lean_expr_mk_app(x_22, x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
x_26 = l___private_Init_Lean_Expr_1__mkAppRangeAux___main(x_6, x_3, x_25, x_23);
x_27 = lean_apply_1(x_7, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_7);
x_30 = lean_box(0);
x_31 = lean_apply_1(x_1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_apply_1(x_1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_apply_1(x_1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_apply_1(x_1, x_38);
return x_39;
}
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_21; lean_object* x_22; 
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_22 = lean_box(x_21);
switch (lean_obj_tag(x_22)) {
case 2:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_unsigned_to_nat(3u);
x_9 = x_23;
x_10 = x_24;
goto block_20;
}
case 3:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(4u);
x_26 = lean_unsigned_to_nat(3u);
x_9 = x_25;
x_10 = x_26;
goto block_20;
}
default: 
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_7, x_27);
return x_28;
}
}
block_20:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_6, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_2, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_18, 0, x_7);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_6);
lean_closure_set(x_18, 3, x_10);
lean_closure_set(x_18, 4, x_9);
lean_closure_set(x_18, 5, x_11);
lean_closure_set(x_18, 6, x_8);
x_19 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_reduceQuotRecAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceQuotRecAux___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceQuotRecAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_reduceQuotRecAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_reduceQuotRecAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_reduceQuotRecAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceQuotRecAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
if (lean_obj_tag(x_11) == 4)
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
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_QuotUtil_1__matchQuotRecApp___rarg), 4, 0);
return x_4;
}
}
lean_object* l___private_Init_Lean_QuotUtil_1__matchQuotRecApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_QuotUtil_1__matchQuotRecApp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_reduceQuotRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn___main(x_4);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = lean_environment_find(x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_5, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_4, x_15);
x_17 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_4, x_18, x_20);
x_22 = l_Lean_reduceQuotRecAux___rarg(x_1, x_2, x_3, x_14, x_9, x_21, x_5, x_6);
lean_dec(x_9);
lean_dec(x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_5, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_5, x_25);
return x_26;
}
}
}
lean_object* l_Lean_reduceQuotRec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_reduceQuotRec___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_reduceQuotRec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_reduceQuotRec(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_isQuotRecStuck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_environment_find(x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_6 = x_15;
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_18);
x_20 = l_Lean_exprIsInhabited___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
x_24 = l___private_Init_Lean_Expr_2__getAppArgsAux___main(x_5, x_21, x_23);
x_25 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
x_26 = lean_box(x_25);
switch (lean_obj_tag(x_26)) {
case 2:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_24);
x_28 = lean_unsigned_to_nat(5u);
x_29 = lean_nat_dec_lt(x_28, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_6 = x_30;
goto block_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_array_fget(x_24, x_28);
lean_dec(x_24);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_apply_1(x_2, x_31);
x_34 = lean_apply_4(x_32, lean_box(0), lean_box(0), x_33, x_3);
return x_34;
}
}
case 3:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_array_get_size(x_24);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_dec_lt(x_36, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_6 = x_38;
goto block_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_fget(x_24, x_36);
lean_dec(x_24);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_apply_1(x_2, x_39);
x_42 = lean_apply_4(x_40, lean_box(0), lean_box(0), x_41, x_3);
return x_42;
}
}
default: 
{
lean_object* x_43; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
x_6 = x_43;
goto block_11;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_6 = x_44;
goto block_11;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(0);
x_6 = x_45;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Lean_isQuotRecStuck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isQuotRecStuck___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_isQuotRecStuck___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isQuotRecStuck(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_QuotUtil(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
