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
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsInt___boxed(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denote(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instBEqExpr;
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158____boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instBEqExpr___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Var_denote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
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
LEAN_EXPORT uint8_t l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_nat_dec_eq(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_nat_dec_eq(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_3 = x_20;
x_4 = x_21;
x_5 = x_22;
x_6 = x_23;
goto block_9;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_3 = x_26;
x_4 = x_27;
x_5 = x_28;
x_6 = x_29;
goto block_9;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_3 = x_32;
x_4 = x_33;
x_5 = x_34;
x_6 = x_35;
goto block_9;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
return x_37;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_3 = x_38;
x_4 = x_39;
x_5 = x_40;
x_6 = x_41;
goto block_9;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(0);
x_43 = lean_unbox(x_42);
return x_43;
}
}
default: 
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158_(x_44, x_46);
if (x_48 == 0)
{
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_eq(x_45, x_47);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
return x_51;
}
}
}
block_9:
{
uint8_t x_7; 
x_7 = l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158_(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Int_OfNat_instBEqExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_OfNat_beqExpr____x40_Init_Data_Int_OfNat___hyg_158____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_OfNat_instBEqExpr___closed__0;
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
x_5 = l_Lean_RArray_getImpl___redArg(x_1, x_4);
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
case 5:
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
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = l_Int_OfNat_Expr_denote(x_1, x_26);
x_29 = lean_nat_pow(x_28, x_27);
lean_dec(x_28);
return x_29;
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
x_6 = l_Lean_RArray_getImpl___redArg(x_1, x_5);
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
case 5:
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
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = l_Int_OfNat_Expr_denoteAsInt(x_1, x_28);
x_31 = l_Int_pow(x_30, x_29);
lean_dec(x_29);
lean_dec(x_30);
return x_31;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_4, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_2(x_5, x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_2(x_6, x_19, x_20);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_7, x_22, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_2(x_8, x_25, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Int_OfNat_0__Int_OfNat_Expr_denote_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
l_Int_OfNat_instBEqExpr___closed__0 = _init_l_Int_OfNat_instBEqExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_instBEqExpr___closed__0);
l_Int_OfNat_instBEqExpr = _init_l_Int_OfNat_instBEqExpr();
lean_mark_persistent(l_Int_OfNat_instBEqExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
