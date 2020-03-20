// Lean compiler output
// Module: Init.Lean.Util.Recognizers
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___closed__1;
lean_object* l_Lean_Expr_prod_x3f___closed__2;
lean_object* l_Lean_Expr_iff_x3f(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_listLitAux___main___closed__5;
lean_object* l_Lean_Expr_app4_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_listLit_x3f(lean_object*);
lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Expr_iff_x3f___closed__2;
lean_object* l_Lean_Expr_heq_x3f(lean_object*);
lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eq_x3f(lean_object*);
lean_object* l_Lean_Expr_iff_x3f___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_iff_x3f___closed__1;
lean_object* l_Lean_Expr_app2_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLitAux___main___closed__4;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLitAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app3_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_heq_x3f___closed__1;
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLitAux___main___closed__6;
lean_object* l_Lean_Expr_arrow_x3f(lean_object*);
lean_object* l_Lean_Expr_listLitAux___main___closed__2;
lean_object* l_Lean_Expr_app1_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f___closed__1;
lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_prod_x3f___closed__1;
lean_object* l_Lean_Expr_arrayLit_x3f___closed__2;
lean_object* l_Lean_Expr_prod_x3f(lean_object*);
lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_listLitAux___main___closed__3;
lean_object* l_Lean_Expr_listLitAux___main___closed__1;
lean_object* l_Lean_Expr_app1_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app1_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_app2_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app2_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_app3_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Expr_app3_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app3_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_app4_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appFn_x21(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_11 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Expr_app4_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app4_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_eq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_eq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_eq_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_eq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_eq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_eq_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_iff_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Iff");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_iff_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_iff_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_iff_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_iff_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Expr_iff_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_iff_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_heq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HEq");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_heq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_heq_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_heq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_heq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appFn_x21(x_6);
x_8 = l_Lean_Expr_appFn_x21(x_7);
x_9 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_11 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_12 = l_Lean_Expr_appArg_x21(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_heq_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_arrow_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_hasLooseBVars(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_arrow_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_listLitAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_listLitAux___main___closed__2;
x_2 = l_Lean_Expr_listLitAux___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cons");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_listLitAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_listLitAux___main___closed__2;
x_2 = l_Lean_Expr_listLitAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_listLitAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Expr_listLitAux___main___closed__4;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity___main(x_1, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Expr_listLitAux___main___closed__6;
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_Lean_Expr_isAppOfArity___main(x_1, x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Expr_appArg_x21(x_1);
x_11 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_10;
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_List_reverse___rarg(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Expr_listLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_listLitAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_listLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Expr_listLitAux___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_arrayLit_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArray");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_arrayLit_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_listLitAux___main___closed__2;
x_2 = l_Lean_Expr_arrayLit_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_arrayLit_x3f___closed__2;
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Expr_isAppOfArity___main(x_1, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
x_2 = x_11;
goto block_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_2 = x_16;
goto block_7;
}
block_7:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Expr_listLit_x3f(x_5);
return x_6;
}
}
}
}
lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_arrayLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_prod_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_prod_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_prod_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_prod_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_prod_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_appFn_x21(x_1);
x_7 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_prod_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_Recognizers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_eq_x3f___closed__1 = _init_l_Lean_Expr_eq_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_eq_x3f___closed__1);
l_Lean_Expr_eq_x3f___closed__2 = _init_l_Lean_Expr_eq_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_eq_x3f___closed__2);
l_Lean_Expr_iff_x3f___closed__1 = _init_l_Lean_Expr_iff_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_iff_x3f___closed__1);
l_Lean_Expr_iff_x3f___closed__2 = _init_l_Lean_Expr_iff_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_iff_x3f___closed__2);
l_Lean_Expr_heq_x3f___closed__1 = _init_l_Lean_Expr_heq_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_heq_x3f___closed__1);
l_Lean_Expr_heq_x3f___closed__2 = _init_l_Lean_Expr_heq_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_heq_x3f___closed__2);
l_Lean_Expr_listLitAux___main___closed__1 = _init_l_Lean_Expr_listLitAux___main___closed__1();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__1);
l_Lean_Expr_listLitAux___main___closed__2 = _init_l_Lean_Expr_listLitAux___main___closed__2();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__2);
l_Lean_Expr_listLitAux___main___closed__3 = _init_l_Lean_Expr_listLitAux___main___closed__3();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__3);
l_Lean_Expr_listLitAux___main___closed__4 = _init_l_Lean_Expr_listLitAux___main___closed__4();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__4);
l_Lean_Expr_listLitAux___main___closed__5 = _init_l_Lean_Expr_listLitAux___main___closed__5();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__5);
l_Lean_Expr_listLitAux___main___closed__6 = _init_l_Lean_Expr_listLitAux___main___closed__6();
lean_mark_persistent(l_Lean_Expr_listLitAux___main___closed__6);
l_Lean_Expr_arrayLit_x3f___closed__1 = _init_l_Lean_Expr_arrayLit_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_arrayLit_x3f___closed__1);
l_Lean_Expr_arrayLit_x3f___closed__2 = _init_l_Lean_Expr_arrayLit_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_arrayLit_x3f___closed__2);
l_Lean_Expr_prod_x3f___closed__1 = _init_l_Lean_Expr_prod_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_prod_x3f___closed__1);
l_Lean_Expr_prod_x3f___closed__2 = _init_l_Lean_Expr_prod_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_prod_x3f___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
