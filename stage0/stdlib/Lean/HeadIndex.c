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
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_head___boxed(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1871_(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_head(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_HeadIndex_hash___boxed(lean_object*);
static lean_object* l_Lean_HeadIndex_instHashableHeadIndex___closed__1;
LEAN_EXPORT uint64_t l_Lean_HeadIndex_HeadIndex_hash(lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_instHashableHeadIndex;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_484_(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedHeadIndex;
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
static lean_object* l_Lean_instInhabitedHeadIndex___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex;
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(lean_object*, lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
static lean_object* l_Lean_instBEqHeadIndex___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3;
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4;
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
LEAN_EXPORT uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(lean_object* x_1, lean_object* x_2) {
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
x_25 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(x_23, x_24);
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
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l_Lean_HeadIndex_HeadIndex_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 11;
x_4 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1871_(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 13;
x_8 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_484_(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = 17;
x_12 = l_Lean_Name_hash(x_10);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = 19;
x_17 = l_Lean_Name_hash(x_14);
x_18 = lean_uint64_of_nat(x_15);
x_19 = lean_uint64_mix_hash(x_17, x_18);
x_20 = lean_uint64_mix_hash(x_16, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = 23;
x_23 = l_Lean_Literal_hash(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
return x_24;
}
case 5:
{
uint64_t x_25; 
x_25 = 29;
return x_25;
}
case 6:
{
uint64_t x_26; 
x_26 = 31;
return x_26;
}
default: 
{
uint64_t x_27; 
x_27 = 37;
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_HeadIndex_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_HeadIndex_HeadIndex_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_HeadIndex_instHashableHeadIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HeadIndex_HeadIndex_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_HeadIndex_instHashableHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_HeadIndex_instHashableHeadIndex___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_head(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_head___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_head(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(5);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(6);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(7);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; 
x_9 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1;
return x_9;
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
x_1 = x_13;
goto _start;
}
case 6:
{
lean_object* x_15; 
x_15 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2;
return x_15;
}
case 7:
{
lean_object* x_16; 
x_16 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3;
return x_16;
}
case 8:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 3);
x_1 = x_17;
goto _start;
}
case 9:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedHeadIndex;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.HeadIndex");
return x_1;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.HeadIndex.0.Lean.Expr.toHeadIndexSlow");
return x_1;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected expression kind");
return x_1;
}
}
static lean_object* _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1;
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2;
x_3 = lean_unsigned_to_nat(94u);
x_4 = lean_unsigned_to_nat(31u);
x_5 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
lean_dec(x_1);
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4;
x_3 = l_panic___at___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(5);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_1 = x_11;
goto _start;
}
case 6:
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(6);
return x_13;
}
case 7:
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(7);
return x_14;
}
case 8:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_expr_instantiate1(x_16, x_15);
lean_dec(x_15);
lean_dec(x_16);
x_1 = x_17;
goto _start;
}
case 9:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
case 10:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_1 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(x_1);
return x_3;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
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
l_Lean_HeadIndex_instHashableHeadIndex___closed__1 = _init_l_Lean_HeadIndex_instHashableHeadIndex___closed__1();
lean_mark_persistent(l_Lean_HeadIndex_instHashableHeadIndex___closed__1);
l_Lean_HeadIndex_instHashableHeadIndex = _init_l_Lean_HeadIndex_instHashableHeadIndex();
lean_mark_persistent(l_Lean_HeadIndex_instHashableHeadIndex);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__1);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__2);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___closed__3);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__1);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__2);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__3);
l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4 = _init_l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4();
lean_mark_persistent(l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
