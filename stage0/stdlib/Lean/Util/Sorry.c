// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: Lean.Util.FindExpr Lean.Declaration
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
static lean_object* l_Lean_Expr_hasSyntheticSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_isNonSyntheticSorry___closed__1;
static lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_hasSorry___closed__1;
static lean_object* l_Lean_Expr_isSorry___closed__1;
static lean_object* l_Lean_Expr_hasNonSyntheticSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_isSyntheticSorry___closed__2;
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_hasSorry___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2(uint8_t, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Expr_isSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sorryAx", 7, 7);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = l_Lean_Expr_isSorry___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isSyntheticSorry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_isSorry___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_isSyntheticSorry___closed__2;
x_20 = lean_string_dec_eq(x_14, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
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
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isNonSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_isSorry___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_isNonSyntheticSorry___closed__1;
x_20 = lean_string_dec_eq(x_14, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
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
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isNonSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_hasSorry___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSorry___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_hasSorry___lambda__1___closed__1;
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_hasSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hasSorry___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry___closed__1;
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_hasSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_isSyntheticSorry___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry___closed__1;
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_hasNonSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_isNonSyntheticSorry___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasNonSyntheticSorry___closed__1;
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasNonSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
x_7 = l_Lean_Expr_hasSorry(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Expr_hasSorry(x_8);
x_1 = x_9;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
x_1 = x_11;
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = 1;
x_1 = x_14;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasSorry(x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = 1;
x_1 = x_9;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Expr_hasSorry(x_6);
x_8 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3(x_7, x_5);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_10, 2);
x_13 = 1;
x_14 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3(x_13, x_12);
x_1 = x_14;
x_2 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_Expr_hasSorry(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
case 4:
{
return x_2;
}
case 5:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2(x_2, x_8);
return x_9;
}
case 6:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4(x_2, x_10);
return x_11;
}
default: 
{
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_13, 2);
x_16 = l_Lean_Expr_hasSorry(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasSorry(x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasSorry___spec__4(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Declaration_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
x_7 = l_Lean_Expr_hasNonSyntheticSorry(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Expr_hasNonSyntheticSorry(x_8);
x_1 = x_9;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
x_1 = x_11;
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = 1;
x_1 = x_14;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = 1;
x_1 = x_9;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Expr_hasNonSyntheticSorry(x_6);
x_8 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3(x_7, x_5);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_10, 2);
x_13 = 1;
x_14 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3(x_13, x_12);
x_1 = x_14;
x_2 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
case 4:
{
return x_2;
}
case 5:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2(x_2, x_8);
return x_9;
}
case 6:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4(x_2, x_10);
return x_11;
}
default: 
{
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_13, 2);
x_16 = l_Lean_Expr_hasNonSyntheticSorry(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasNonSyntheticSorry(x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldlM___at_Lean_Declaration_hasNonSyntheticSorry___spec__4(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasNonSyntheticSorry___spec__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Declaration_hasNonSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_isSorry___closed__1 = _init_l_Lean_Expr_isSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSorry___closed__1);
l_Lean_Expr_isSyntheticSorry___closed__1 = _init_l_Lean_Expr_isSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSyntheticSorry___closed__1);
l_Lean_Expr_isSyntheticSorry___closed__2 = _init_l_Lean_Expr_isSyntheticSorry___closed__2();
lean_mark_persistent(l_Lean_Expr_isSyntheticSorry___closed__2);
l_Lean_Expr_isNonSyntheticSorry___closed__1 = _init_l_Lean_Expr_isNonSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isNonSyntheticSorry___closed__1);
l_Lean_Expr_hasSorry___lambda__1___closed__1 = _init_l_Lean_Expr_hasSorry___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_hasSorry___lambda__1___closed__1);
l_Lean_Expr_hasSorry___closed__1 = _init_l_Lean_Expr_hasSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_hasSorry___closed__1);
l_Lean_Expr_hasSyntheticSorry___closed__1 = _init_l_Lean_Expr_hasSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_hasSyntheticSorry___closed__1);
l_Lean_Expr_hasNonSyntheticSorry___closed__1 = _init_l_Lean_Expr_hasNonSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_hasNonSyntheticSorry___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
