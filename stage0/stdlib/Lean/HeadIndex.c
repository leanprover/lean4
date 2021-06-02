// Lean compiler output
// Module: Lean.HeadIndex
// Imports: Init Lean.Expr
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
lean_object* l_Lean_Expr_toHeadIndex___boxed(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___closed__1;
lean_object* l_Lean_Expr_toHeadIndex___closed__2;
lean_object* l_Lean_Expr_head___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___closed__4;
lean_object* l_Lean_HeadIndex_instHashableUSizeHeadIndex;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_head(lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux_match__1(lean_object*);
lean_object* l_Lean_HeadIndex_HeadIndex_hash___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___closed__3;
lean_object* l_Lean_Expr_head_match__1(lean_object*);
lean_object* l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1;
size_t l_Lean_HeadIndex_HeadIndex_hash(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30_(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HeadIndex_HeadIndex_hash_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedHeadIndex;
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_instInhabitedHeadIndex___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65__match__1(lean_object*);
lean_object* l_Lean_instBEqHeadIndex;
lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65_(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Literal_hash(lean_object*);
lean_object* l_Lean_HeadIndex_HeadIndex_hash_match__1(lean_object*);
lean_object* l_Lean_instBEqHeadIndex___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_head_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65____boxed(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Expr_toHeadIndex_match__1(lean_object*);
static lean_object* _init_l_Lean_instInhabitedHeadIndex___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedHeadIndex___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_3, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_apply_2(x_11, x_1, x_2);
return x_15;
}
}
case 1:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_4, x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_apply_2(x_11, x_1, x_2);
return x_19;
}
}
case 2:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_2(x_5, x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_5);
x_23 = lean_apply_2(x_11, x_1, x_2);
return x_23;
}
}
case 3:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_4(x_6, x_24, x_25, x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_6);
x_29 = lean_apply_2(x_11, x_1, x_2);
return x_29;
}
}
case 4:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_apply_2(x_7, x_30, x_31);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_7);
x_33 = lean_apply_2(x_11, x_1, x_2);
return x_33;
}
}
case 5:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_8, x_34);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_8);
x_36 = lean_apply_2(x_11, x_1, x_2);
return x_36;
}
}
case 6:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
x_37 = lean_box(0);
x_38 = lean_apply_1(x_9, x_37);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_9);
x_39 = lean_apply_2(x_11, x_1, x_2);
return x_39;
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
x_40 = lean_box(0);
x_41 = lean_apply_1(x_10, x_40);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_10);
x_42 = lean_apply_2(x_11, x_1, x_2);
return x_42;
}
}
}
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65__match__1___rarg), 11, 0);
return x_2;
}
}
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65_(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_name_eq(x_3, x_4);
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
x_9 = lean_name_eq(x_7, x_8);
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_name_eq(x_11, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_name_eq(x_15, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_16, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_2, 0);
x_25 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30_(x_23, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
default: 
{
if (lean_obj_tag(x_2) == 7)
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
else
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqHeadIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqHeadIndex___closed__1;
return x_1;
}
}
lean_object* l_Lean_HeadIndex_HeadIndex_hash_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_apply_1(x_6, x_19);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_7, x_21);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_8, x_23);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_9, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_HeadIndex_HeadIndex_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HeadIndex_HeadIndex_hash_match__1___rarg), 9, 0);
return x_2;
}
}
size_t l_Lean_HeadIndex_HeadIndex_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; size_t x_3; size_t x_4; size_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 11;
x_4 = l_Lean_Name_hash(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 13;
x_8 = l_Lean_Name_hash(x_6);
x_9 = lean_usize_mix_hash(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = 17;
x_12 = l_Lean_Name_hash(x_10);
x_13 = lean_usize_mix_hash(x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = 19;
x_17 = l_Lean_Name_hash(x_14);
x_18 = lean_usize_of_nat(x_15);
x_19 = lean_usize_mix_hash(x_17, x_18);
x_20 = lean_usize_mix_hash(x_16, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = 23;
x_23 = l_Lean_Literal_hash(x_21);
x_24 = lean_usize_mix_hash(x_22, x_23);
return x_24;
}
case 5:
{
size_t x_25; 
x_25 = 29;
return x_25;
}
case 6:
{
size_t x_26; 
x_26 = 31;
return x_26;
}
default: 
{
size_t x_27; 
x_27 = 37;
return x_27;
}
}
}
}
lean_object* l_Lean_HeadIndex_HeadIndex_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_HeadIndex_HeadIndex_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HeadIndex_HeadIndex_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_HeadIndex_instHashableUSizeHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_head_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_3(x_2, x_6, x_7, x_9);
return x_10;
}
case 8:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_5(x_3, x_11, x_12, x_13, x_14, x_16);
return x_17;
}
case 10:
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_21 = lean_box_uint64(x_20);
x_22 = lean_apply_3(x_4, x_18, x_19, x_21);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_apply_1(x_5, x_1);
return x_23;
}
}
}
}
lean_object* l_Lean_Expr_head_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_head_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_head(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 8:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
x_1 = x_4;
goto _start;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
lean_object* l_Lean_Expr_head___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_head(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_4(x_3, x_7, x_8, x_10, x_2);
return x_11;
}
case 8:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_6(x_4, x_12, x_13, x_14, x_15, x_17, x_2);
return x_18;
}
case 10:
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_4(x_5, x_19, x_20, x_22, x_2);
return x_23;
}
default: 
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_apply_2(x_6, x_1, x_2);
return x_24;
}
}
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
case 8:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
x_1 = x_7;
goto _start;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
x_1 = x_9;
goto _start;
}
default: 
{
return x_2;
}
}
}
}
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_headNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_toHeadIndex_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_1);
return x_14;
}
case 1:
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_2(x_3, x_15, x_17);
return x_18;
}
case 2:
{
lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_21 = lean_box_uint64(x_20);
x_22 = lean_apply_2(x_2, x_19, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_2(x_6, x_23, x_25);
return x_26;
}
case 4:
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_3(x_4, x_27, x_28, x_30);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_35 = lean_box_uint64(x_34);
x_36 = lean_apply_3(x_10, x_32, x_33, x_35);
return x_36;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_41 = lean_box_uint64(x_40);
x_42 = lean_apply_4(x_7, x_37, x_38, x_39, x_41);
return x_42;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_4(x_8, x_43, x_44, x_45, x_47);
return x_48;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc(x_52);
x_53 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_54 = lean_box_uint64(x_53);
x_55 = lean_apply_5(x_11, x_49, x_50, x_51, x_52, x_54);
return x_55;
}
case 9:
{
lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_13);
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
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_58 = lean_box_uint64(x_57);
x_59 = lean_apply_2(x_9, x_56, x_58);
return x_59;
}
case 10:
{
lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_63 = lean_box_uint64(x_62);
x_64 = lean_apply_3(x_12, x_60, x_61, x_63);
return x_64;
}
default: 
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_69 = lean_box_uint64(x_68);
x_70 = lean_apply_4(x_5, x_65, x_66, x_67, x_69);
return x_70;
}
}
}
}
lean_object* l_Lean_Expr_toHeadIndex_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_toHeadIndex_match__1___rarg), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_toHeadIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.HeadIndex");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_toHeadIndex___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.toHeadIndex");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_toHeadIndex___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected expression kind");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_toHeadIndex___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_toHeadIndex___closed__1;
x_2 = l_Lean_Expr_toHeadIndex___closed__2;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(31u);
x_5 = l_Lean_Expr_toHeadIndex___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_toHeadIndex(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedHeadIndex;
x_3 = l_Lean_Expr_toHeadIndex___closed__4;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; 
x_9 = lean_box(5);
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
case 5:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
x_1 = x_12;
goto _start;
}
case 6:
{
lean_object* x_14; 
x_14 = lean_box(6);
return x_14;
}
case 7:
{
lean_object* x_15; 
x_15 = lean_box(7);
return x_15;
}
case 8:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 3);
x_1 = x_16;
goto _start;
}
case 9:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 10:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
x_1 = x_20;
goto _start;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
x_24 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Expr_toHeadIndex___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_toHeadIndex(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_HeadIndex(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedHeadIndex___closed__1 = _init_l_Lean_instInhabitedHeadIndex___closed__1();
lean_mark_persistent(l_Lean_instInhabitedHeadIndex___closed__1);
l_Lean_instInhabitedHeadIndex = _init_l_Lean_instInhabitedHeadIndex();
lean_mark_persistent(l_Lean_instInhabitedHeadIndex);
l_Lean_instBEqHeadIndex___closed__1 = _init_l_Lean_instBEqHeadIndex___closed__1();
lean_mark_persistent(l_Lean_instBEqHeadIndex___closed__1);
l_Lean_instBEqHeadIndex = _init_l_Lean_instBEqHeadIndex();
lean_mark_persistent(l_Lean_instBEqHeadIndex);
l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1 = _init_l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1();
lean_mark_persistent(l_Lean_HeadIndex_instHashableUSizeHeadIndex___closed__1);
l_Lean_HeadIndex_instHashableUSizeHeadIndex = _init_l_Lean_HeadIndex_instHashableUSizeHeadIndex();
lean_mark_persistent(l_Lean_HeadIndex_instHashableUSizeHeadIndex);
l_Lean_Expr_toHeadIndex___closed__1 = _init_l_Lean_Expr_toHeadIndex___closed__1();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___closed__1);
l_Lean_Expr_toHeadIndex___closed__2 = _init_l_Lean_Expr_toHeadIndex___closed__2();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___closed__2);
l_Lean_Expr_toHeadIndex___closed__3 = _init_l_Lean_Expr_toHeadIndex___closed__3();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___closed__3);
l_Lean_Expr_toHeadIndex___closed__4 = _init_l_Lean_Expr_toHeadIndex___closed__4();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
