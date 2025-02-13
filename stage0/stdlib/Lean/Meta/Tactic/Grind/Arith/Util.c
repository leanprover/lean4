// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Util
// Imports: Lean.Expr Lean.Message
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
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2(lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_isNatType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2;
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isNatType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType___closed__2;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instHAdd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instAddNat", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_appArg(x_2, lean_box(0));
x_6 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_Expr_appArg(x_6, lean_box(0));
x_10 = l_Lean_Expr_appFnCleanup(x_6, lean_box(0));
x_11 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2;
x_12 = l_Lean_Expr_isConstOf(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_Meta_Grind_Arith_isNatType(x_9);
lean_dec(x_9);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4;
x_17 = l_Lean_Expr_isConstOf(x_5, x_16);
lean_dec(x_5);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instLENat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat___closed__2;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_appArg(x_2, lean_box(0));
x_6 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appArg(x_6, lean_box(0));
x_10 = l_Lean_Expr_appFnCleanup(x_6, lean_box(0));
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_appArg(x_10, lean_box(0));
x_14 = l_Lean_Expr_appFnCleanup(x_10, lean_box(0));
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup(x_14, lean_box(0));
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup(x_17, lean_box(0));
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Expr_appFnCleanup(x_20, lean_box(0));
x_24 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_13);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_5);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup(x_5, lean_box(0));
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_appArg(x_8, lean_box(0));
x_12 = l_Lean_Expr_appFnCleanup(x_8, lean_box(0));
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_12);
lean_dec(x_11);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_appFnCleanup(x_12, lean_box(0));
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_15);
lean_dec(x_11);
x_17 = 0;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_11);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_22 = l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_11);
x_24 = 0;
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_11);
return x_25;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_tag(x_2, 1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instOfNatNat", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1;
x_3 = l_Lean_Expr_cleanupAnnotations(x_1);
x_4 = l_Lean_Expr_isApp(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Expr_appArg(x_3, lean_box(0));
x_7 = l_Lean_Expr_appFnCleanup(x_3, lean_box(0));
x_8 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5;
x_9 = l_Lean_Expr_isConstOf(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_apply_1(x_2, x_6);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1;
x_3 = l_Lean_Expr_cleanupAnnotations(x_1);
x_4 = l_Lean_Expr_isApp(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Expr_appArg(x_3, lean_box(0));
x_7 = l_Lean_Expr_appFnCleanup(x_3, lean_box(0));
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_appFnCleanup(x_7, lean_box(0));
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_6);
x_12 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Expr_appFnCleanup(x_10, lean_box(0));
x_14 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4;
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3;
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_apply_1(x_2, x_6);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_isNatType___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatType___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatType___closed__1);
l_Lean_Meta_Grind_Arith_isNatType___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatType___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatType___closed__2);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__1);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__2);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__3);
l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4 = _init_l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstAddNat___closed__4);
l_Lean_Meta_Grind_Arith_isInstLENat___closed__1 = _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstLENat___closed__1);
l_Lean_Meta_Grind_Arith_isInstLENat___closed__2 = _init_l_Lean_Meta_Grind_Arith_isInstLENat___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isInstLENat___closed__2);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__1);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__2);
l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatAdd_x3f___closed__3);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__1);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__2);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__3);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__4);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___lambda__3___closed__5);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__1);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__2);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__3);
l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4 = _init_l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_isNatNum_x3f___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
