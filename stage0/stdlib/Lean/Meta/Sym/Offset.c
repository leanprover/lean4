// Lean compiler output
// Module: Lean.Meta.Sym.Offset
// Imports: public import Lean.Meta.Sym.LitValues
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
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset___closed__0;
static lean_object* l_Lean_Meta_Sym_isOffset___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__5;
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__2;
static lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedOffset;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object*);
static lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_Offset_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Sym_Offset_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Sym_Offset_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Sym_Offset_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_Offset_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Sym_Offset_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_Offset_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedOffset_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedOffset() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedOffset_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_add(x_6, x_2);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_nat_add(x_10, x_2);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_nat_add(x_13, x_2);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Sym_Offset_inc(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_isOffset_x3f___closed__1;
x_2 = l_Lean_Meta_Sym_isOffset_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_isOffset_x3f___closed__4;
x_2 = l_Lean_Meta_Sym_isOffset_x3f___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Sym_isOffset_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
x_8 = l_Lean_Expr_isConstOf(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isApp(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_11);
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_21);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_26 = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
lean_dec_ref(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_24);
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Meta_Sym_isOffset_x3f___closed__6;
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
lean_dec_ref(x_24);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec_ref(x_11);
lean_dec_ref(x_5);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Sym_getNatValue_x3f(x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_11);
x_33 = lean_box(0);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(x_11);
x_37 = l_Lean_Meta_Sym_Offset_inc(x_36, x_35);
lean_dec(x_35);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(x_11);
x_40 = l_Lean_Meta_Sym_Offset_inc(x_39, x_38);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
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
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_6);
x_42 = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(x_5);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Meta_Sym_Offset_inc(x_42, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc_ref(x_1);
x_2 = l_Lean_Meta_Sym_isOffset_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
x_10 = lean_name_eq(x_1, x_9);
x_3 = x_10;
goto block_6;
}
else
{
x_3 = x_8;
goto block_6;
}
block_6:
{
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Sym_isOffset_x3f(x_2);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Sym_isOffset_x3f_x27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_isOffset___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Sym_isOffset___closed__1;
x_2 = l_Lean_Meta_Sym_isOffset___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
x_7 = l_Lean_Expr_isConstOf(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_5);
if (x_8 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec_ref(x_9);
lean_dec_ref(x_4);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_4);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
lean_dec_ref(x_18);
if (x_20 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_4);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Meta_Sym_isOffset_x3f___closed__6;
x_22 = l_Lean_Expr_isConstOf(x_17, x_21);
lean_dec_ref(x_17);
if (x_22 == 0)
{
lean_dec_ref(x_4);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_cleanupAnnotations(x_4);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Meta_Sym_isOffset___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec_ref(x_27);
return x_32;
}
else
{
if (lean_obj_tag(x_27) == 9)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
return x_22;
}
else
{
lean_dec_ref(x_33);
return x_7;
}
}
else
{
lean_dec_ref(x_27);
return x_7;
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
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Sym_isOffset(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
x_9 = lean_name_eq(x_1, x_8);
x_3 = x_9;
goto block_5;
}
else
{
x_3 = x_7;
goto block_5;
}
block_5:
{
if (x_3 == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l_Lean_Meta_Sym_isOffset(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Sym_isOffset_x27(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object* x_1) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc_ref(x_1);
x_8 = l_Lean_Expr_cleanupAnnotations(x_1);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_dec_ref(x_8);
goto block_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = l_Lean_Meta_Sym_isOffset_x3f___closed__2;
x_13 = l_Lean_Expr_isConstOf(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isApp(x_11);
if (x_14 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Meta_Sym_isOffset___closed__2;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isApp(x_18);
if (x_21 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_15);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Meta_Sym_isOffset_x3f___closed__5;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec_ref(x_26);
if (x_28 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_10);
goto block_4;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Meta_Sym_getNatValue_x3f(x_10);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Sym_toOffset(x_15);
x_32 = l_Lean_Meta_Sym_Offset_inc(x_31, x_30);
lean_dec(x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec_ref(x_15);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_10);
if (lean_obj_tag(x_15) == 9)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_35);
lean_dec_ref(x_15);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_dec_ref(x_35);
goto block_7;
}
}
else
{
lean_dec_ref(x_15);
goto block_7;
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_11);
lean_dec_ref(x_1);
x_39 = l_Lean_Meta_Sym_toOffset(x_10);
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Meta_Sym_Offset_inc(x_39, x_40);
return x_41;
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0 = _init_l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0);
l_Lean_Meta_Sym_instInhabitedOffset_default = _init_l_Lean_Meta_Sym_instInhabitedOffset_default();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedOffset_default);
l_Lean_Meta_Sym_instInhabitedOffset = _init_l_Lean_Meta_Sym_instInhabitedOffset();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedOffset);
l_Lean_Meta_Sym_isOffset_x3f___closed__1 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__1);
l_Lean_Meta_Sym_isOffset_x3f___closed__0 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__0);
l_Lean_Meta_Sym_isOffset_x3f___closed__2 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__2);
l_Lean_Meta_Sym_isOffset_x3f___closed__4 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__4);
l_Lean_Meta_Sym_isOffset_x3f___closed__3 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__3);
l_Lean_Meta_Sym_isOffset_x3f___closed__5 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__5);
l_Lean_Meta_Sym_isOffset_x3f___closed__6 = _init_l_Lean_Meta_Sym_isOffset_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset_x3f___closed__6);
l_Lean_Meta_Sym_isOffset___closed__0 = _init_l_Lean_Meta_Sym_isOffset___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset___closed__0);
l_Lean_Meta_Sym_isOffset___closed__1 = _init_l_Lean_Meta_Sym_isOffset___closed__1();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset___closed__1);
l_Lean_Meta_Sym_isOffset___closed__2 = _init_l_Lean_Meta_Sym_isOffset___closed__2();
lean_mark_persistent(l_Lean_Meta_Sym_isOffset___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
