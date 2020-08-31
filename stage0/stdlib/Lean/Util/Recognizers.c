// Lean compiler output
// Module: Lean.Util.Recognizers
// Imports: Init Lean.Environment
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___closed__1;
lean_object* l_Lean_Expr_iff_x3f(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Array_hasQuote___rarg___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Prod_hasQuote___rarg___closed__2;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_app4_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f___closed__4;
lean_object* l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLit_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_isConstructorApp_x3f___closed__2;
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l_Lean_Expr_listLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_listLitAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app3_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_heq_x3f___closed__1;
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_app1_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app2_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrow_x3f(lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f___closed__1;
lean_object* l_Lean_Expr_app1_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f___closed__3;
lean_object* l_Lean_Expr_prod_x3f(lean_object*);
lean_object* l_Lean_Expr_prod_x3f___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_listLitAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__4;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Expr_isAppOfArity___main(x_1, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l___private_Lean_Syntax_8__quoteList___main___rarg___closed__7;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_16 = l_List_reverse___rarg(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
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
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Array_hasQuote___rarg___closed__2;
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
lean_object* l_Lean_Expr_prod_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Prod_hasQuote___rarg___closed__2;
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
lean_object* l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
lean_object* _init_l_Lean_Expr_isConstructorApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_isConstructorApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Expr_isConstructorApp_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_isConstructorApp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("zero");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_isConstructorApp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Expr_isConstructorApp_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_isConstructorApp_x3f___closed__2;
x_8 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_isConstructorApp_x3f___closed__4;
x_10 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_18);
x_20 = lean_nat_dec_eq(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
x_21 = lean_box(0);
return x_21;
}
else
{
return x_13;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 4);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_30);
x_32 = lean_nat_dec_eq(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_25);
x_33 = lean_box(0);
return x_33;
}
else
{
return x_25;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_1);
x_34 = lean_box(0);
return x_34;
}
}
}
}
lean_object* l_Lean_Expr_isConstructorApp_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_isConstructorApp_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_isConstructorApp_x3f___closed__2;
x_8 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = l_Lean_mkNatLit(x_13);
x_15 = l_Lean_mkOptionalNode___closed__2;
x_16 = lean_array_push(x_15, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_21 = l_Lean_mkNatLit(x_20);
x_22 = l_Lean_mkOptionalNode___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_26 = l_Lean_Expr_isConstructorApp_x3f___closed__4;
x_27 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = l_Array_empty___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Array_empty___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_3);
x_37 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_37) == 4)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_2);
x_40 = lean_box(0);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 4);
lean_inc(x_44);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_46);
x_48 = lean_nat_dec_eq(x_45, x_47);
lean_dec(x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_free_object(x_39);
lean_dec(x_42);
lean_dec(x_2);
x_49 = lean_box(0);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_47);
x_51 = lean_mk_array(x_47, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_47, x_52);
lean_dec(x_47);
x_54 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_51, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_39, 0, x_55);
return x_39;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
lean_dec(x_39);
x_57 = lean_ctor_get(x_56, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 4);
lean_inc(x_58);
x_59 = lean_nat_add(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_60);
x_62 = lean_nat_dec_eq(x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_2);
x_63 = lean_box(0);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_61);
x_65 = lean_mk_array(x_61, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_61, x_66);
lean_dec(x_61);
x_68 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_65, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_56);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_box(0);
return x_71;
}
}
}
else
{
lean_object* x_72; 
x_72 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_72) == 4)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Lean_Util_Recognizers_1__getConstructorVal_x3f(x_1, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_2);
x_75 = lean_box(0);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_77, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 4);
lean_inc(x_79);
x_80 = lean_nat_add(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_81);
x_83 = lean_nat_dec_eq(x_80, x_82);
lean_dec(x_80);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_free_object(x_74);
lean_dec(x_77);
lean_dec(x_2);
x_84 = lean_box(0);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_82);
x_86 = lean_mk_array(x_82, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_82, x_87);
lean_dec(x_82);
x_89 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_86, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_77);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_74, 0, x_90);
return x_74;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
lean_dec(x_74);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 4);
lean_inc(x_93);
x_94 = lean_nat_add(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
x_95 = lean_unsigned_to_nat(0u);
x_96 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_95);
x_97 = lean_nat_dec_eq(x_94, x_96);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_96);
lean_dec(x_91);
lean_dec(x_2);
x_98 = lean_box(0);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_96);
x_100 = lean_mk_array(x_96, x_99);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_96, x_101);
lean_dec(x_96);
x_103 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_100, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_72);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_box(0);
return x_106;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Recognizers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
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
l_Lean_Expr_isConstructorApp_x3f___closed__1 = _init_l_Lean_Expr_isConstructorApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_isConstructorApp_x3f___closed__1);
l_Lean_Expr_isConstructorApp_x3f___closed__2 = _init_l_Lean_Expr_isConstructorApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_isConstructorApp_x3f___closed__2);
l_Lean_Expr_isConstructorApp_x3f___closed__3 = _init_l_Lean_Expr_isConstructorApp_x3f___closed__3();
lean_mark_persistent(l_Lean_Expr_isConstructorApp_x3f___closed__3);
l_Lean_Expr_isConstructorApp_x3f___closed__4 = _init_l_Lean_Expr_isConstructorApp_x3f___closed__4();
lean_mark_persistent(l_Lean_Expr_isConstructorApp_x3f___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
