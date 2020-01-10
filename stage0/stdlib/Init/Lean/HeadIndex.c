// Lean compiler output
// Module: Init.Lean.HeadIndex
// Imports: Init.Lean.Expr
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
lean_object* l_Lean_Expr_toHeadIndex___boxed(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main___closed__2;
lean_object* l_Lean_Expr_head___boxed(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main___boxed(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main___closed__1;
lean_object* l_Lean_HeadIndex_HasBeq___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_head___main(lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_head(lean_object*);
lean_object* l_Lean_HeadIndex_Inhabited;
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HeadIndex_HeadIndex_hash___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main___closed__3;
uint8_t l_Lean_Literal_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l_Lean_HeadIndex_HasBeq;
size_t l_Lean_HeadIndex_HeadIndex_hash(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_HeadIndex_Hashable;
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_head___main___boxed(lean_object*);
lean_object* l_Lean_HeadIndex_Hashable___closed__1;
lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object*);
lean_object* l_Lean_HeadIndex_HeadIndex_beq___boxed(lean_object*, lean_object*);
size_t l_Lean_Literal_hash(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* _init_l_Lean_HeadIndex_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(5);
return x_1;
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
lean_object* _init_l_Lean_HeadIndex_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HeadIndex_HeadIndex_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_HeadIndex_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HeadIndex_Hashable___closed__1;
return x_1;
}
}
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object* x_1, lean_object* x_2) {
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
x_25 = l_Lean_Literal_beq(x_23, x_24);
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
lean_object* l_Lean_HeadIndex_HeadIndex_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HeadIndex_HeadIndex_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_HeadIndex_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HeadIndex_HeadIndex_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_HeadIndex_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HeadIndex_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_head___main(lean_object* x_1) {
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
lean_object* l_Lean_Expr_head___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_head___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_head___main(x_1);
return x_2;
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
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_headNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_1, x_2);
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
lean_object* _init_l_Lean_Expr_toHeadIndex___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.HeadIndex");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_toHeadIndex___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected expression kind");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_toHeadIndex___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Expr_toHeadIndex___main___closed__1;
x_2 = lean_unsigned_to_nat(81u);
x_3 = lean_unsigned_to_nat(29u);
x_4 = l_Lean_Expr_toHeadIndex___main___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; 
x_6 = lean_box(5);
return x_6;
}
case 4:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
x_1 = x_9;
goto _start;
}
case 6:
{
lean_object* x_11; 
x_11 = lean_box(6);
return x_11;
}
case 7:
{
lean_object* x_12; 
x_12 = lean_box(7);
return x_12;
}
case 8:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 3);
x_1 = x_13;
goto _start;
}
case 9:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
case 10:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
x_1 = x_17;
goto _start;
}
case 11:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_HeadIndex_Inhabited;
x_23 = l_Lean_Expr_toHeadIndex___main___closed__3;
x_24 = lean_panic_fn(x_22, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Expr_toHeadIndex___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_toHeadIndex___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_toHeadIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_toHeadIndex___main(x_1);
return x_2;
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
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_HeadIndex(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_HeadIndex_Inhabited = _init_l_Lean_HeadIndex_Inhabited();
lean_mark_persistent(l_Lean_HeadIndex_Inhabited);
l_Lean_HeadIndex_Hashable___closed__1 = _init_l_Lean_HeadIndex_Hashable___closed__1();
lean_mark_persistent(l_Lean_HeadIndex_Hashable___closed__1);
l_Lean_HeadIndex_Hashable = _init_l_Lean_HeadIndex_Hashable();
lean_mark_persistent(l_Lean_HeadIndex_Hashable);
l_Lean_HeadIndex_HasBeq___closed__1 = _init_l_Lean_HeadIndex_HasBeq___closed__1();
lean_mark_persistent(l_Lean_HeadIndex_HasBeq___closed__1);
l_Lean_HeadIndex_HasBeq = _init_l_Lean_HeadIndex_HasBeq();
lean_mark_persistent(l_Lean_HeadIndex_HasBeq);
l_Lean_Expr_toHeadIndex___main___closed__1 = _init_l_Lean_Expr_toHeadIndex___main___closed__1();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___main___closed__1);
l_Lean_Expr_toHeadIndex___main___closed__2 = _init_l_Lean_Expr_toHeadIndex___main___closed__2();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___main___closed__2);
l_Lean_Expr_toHeadIndex___main___closed__3 = _init_l_Lean_Expr_toHeadIndex___main___closed__3();
lean_mark_persistent(l_Lean_Expr_toHeadIndex___main___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
