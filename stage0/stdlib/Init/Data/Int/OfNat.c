// Lean compiler output
// Module: Init.Data.Int.OfNat
// Imports: Init.Data.Int.Lemmas Init.Data.Int.DivMod Init.Data.Int.Linear Init.Data.RArray
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
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsInt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___rarg(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114____boxed(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instBEqExpr___closed__1;
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instBEqExpr;
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_OfNat_Var_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(x_11, x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(x_19, x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
else
{
x_1 = x_20;
x_2 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(x_27, x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
else
{
x_1 = x_28;
x_2 = x_30;
goto _start;
}
}
else
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
default: 
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(x_35, x_37);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 0;
return x_40;
}
else
{
x_1 = x_36;
x_2 = x_38;
goto _start;
}
}
else
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Int_OfNat_instBEqExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Data_Int_OfNat_0__Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_114____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_OfNat_instBEqExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_RArray_getImpl___rarg(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Int_OfNat_Expr_denote(x_1, x_6);
x_9 = l_Int_OfNat_Expr_denote(x_1, x_7);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Int_OfNat_Expr_denote(x_1, x_11);
x_14 = l_Int_OfNat_Expr_denote(x_1, x_12);
x_15 = lean_nat_mul(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = l_Int_OfNat_Expr_denote(x_1, x_16);
x_19 = l_Int_OfNat_Expr_denote(x_1, x_17);
x_20 = lean_nat_div(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l_Int_OfNat_Expr_denote(x_1, x_21);
x_24 = l_Int_OfNat_Expr_denote(x_1, x_22);
x_25 = lean_nat_mod(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_OfNat_Expr_denote(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsInt(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_nat_to_int(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_RArray_getImpl___rarg(x_1, x_5);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_8);
x_11 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_9);
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_13);
x_16 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_14);
x_17 = lean_int_mul(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_18);
x_21 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_19);
x_22 = lean_int_ediv(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_23);
x_26 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_24);
x_27 = lean_int_emod(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_4, x_12, x_13);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_5, x_15, x_16);
return x_17;
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_2(x_6, x_18, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_apply_2(x_7, x_21, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___rarg), 7, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_OfNat_instBEqExpr___closed__1 = _init_l_Int_OfNat_instBEqExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_instBEqExpr___closed__1);
l_Int_OfNat_instBEqExpr = _init_l_Int_OfNat_instBEqExpr();
lean_mark_persistent(l_Int_OfNat_instBEqExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
