// Lean compiler output
// Module: Init.Data.Fin.Basic
// Imports: Init.Data.Nat.Div Init.Data.Nat.Bitwise Init.Coe
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
lean_object* l_Fin_modn_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_land_match__1(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__10(lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__3___boxed(lean_object*);
lean_object* l_Fin_decLe___boxed(lean_object*);
lean_object* l_Init_Data_Fin_Basic___instance__11(lean_object*);
lean_object* l_Init_Data_Fin_Basic___instance__11___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Fin_decLt___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Fin_ofNat(lean_object*, lean_object*);
lean_object* l_Fin_elim0___boxed(lean_object*, lean_object*);
lean_object* l_Fin_mod_match__1(lean_object*, lean_object*);
lean_object* l_Fin_land(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__9(lean_object*);
lean_object* l_Fin_coeToNat(lean_object*);
lean_object* l_Fin_mul_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Fin_decLe___rarg(lean_object*, lean_object*);
lean_object* l_Fin_land___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_div(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__3(lean_object*);
lean_object* l_Fin_add_match__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Fin_lor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_ofNat___boxed(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__1(lean_object*);
lean_object* l_Fin_sub_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_modn___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Fin_ofNat_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__8(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Fin_sub_match__1(lean_object*, lean_object*);
lean_object* l_Fin_mod_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_elim0_match__1(lean_object*);
lean_object* l_Fin_coeToNat___boxed(lean_object*);
lean_object* l_Fin_modn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_ofNat_x27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mul_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_div_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Init_Data_Fin_Basic___instance__11___boxed(lean_object*);
lean_object* l_Fin_mul_match__1(lean_object*, lean_object*);
lean_object* l_Fin_div_match__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint8_t l_Fin_decLt___rarg(lean_object*, lean_object*);
lean_object* l_Fin_decLe(lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__4___boxed(lean_object*);
lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_lor_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__2(lean_object*);
lean_object* l_Fin_lor_match__1(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__1___boxed(lean_object*);
lean_object* l_Fin_mod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_lor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__4(lean_object*);
lean_object* l_Fin_elim0_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Fin_div_match__1(lean_object*, lean_object*);
lean_object* l_Fin_decLt(lean_object*);
lean_object* l_Fin_land_match__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__6(lean_object*);
lean_object* l_Fin_add_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__2___boxed(lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__5(lean_object*);
lean_object* l_Fin_modn_match__1(lean_object*, lean_object*);
lean_object* l_Fin_lor(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Fin_elim0(lean_object*, lean_object*);
lean_object* l_Fin_mod(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_mod_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_coeToNat___rarg(lean_object*);
lean_object* l_Fin_decLe___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Fin_modn(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_decLt___boxed(lean_object*);
lean_object* l_Fin_mul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t l_Init_Data_Fin_Basic___instance__11___rarg(lean_object*, lean_object*);
lean_object* l_Fin_add_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_Init_Data_Fin_Basic___instance__7(lean_object*);
lean_object* l_Fin_div___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_sub_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Fin_land_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_coeToNat___rarg___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Fin_coeToNat___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Fin_coeToNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_coeToNat___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Fin_coeToNat___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_coeToNat___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_coeToNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_coeToNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_Init_Data_Fin_Basic___instance__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_Init_Data_Fin_Basic___instance__2(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Fin_decLt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Fin_decLt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_decLt___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Fin_decLt___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Fin_decLt___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Fin_decLt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_decLt(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Fin_decLe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
lean_object* l_Fin_decLe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_decLe___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Fin_decLe___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Fin_decLe___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Fin_decLe___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_decLe(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_elim0_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
lean_object* l_Fin_elim0_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_elim0_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Fin_elim0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l_Fin_elim0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_elim0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Fin_ofNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mod(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_ofNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_ofNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_ofNat_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_2, x_1);
return x_4;
}
}
lean_object* l_Fin_ofNat_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_ofNat_x27(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_add_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_add_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_add_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_add_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_add_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_add(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_add(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_mul_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_mul_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_mul_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_mul_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_mul_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_mul(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_mul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_mul(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_sub_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_sub_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_sub_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_sub_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_sub_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_sub(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_nat_sub(x_1, x_3);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_4);
x_6 = lean_nat_mod(x_5, x_1);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Fin_sub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_sub(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_mod_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_mod_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_mod_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_mod_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_mod_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_mod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mod(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_mod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_mod(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_div_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_div_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_div_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_div_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_div_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_div(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_div(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_div___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_div(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_modn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_3(x_3, x_1, lean_box(0), x_2);
return x_4;
}
}
lean_object* l_Fin_modn_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_modn_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_modn_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_modn_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_modn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mod(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_modn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_modn(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_land_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_land_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_land_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_land_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_land_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_land(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_land(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_land___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_land(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_lor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_4(x_3, x_1, lean_box(0), x_2, lean_box(0));
return x_4;
}
}
lean_object* l_Fin_lor_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Fin_lor_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Fin_lor_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_lor_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Fin_lor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_lor(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Fin_lor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_lor(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_Init_Data_Fin_Basic___instance__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Fin_ofNat(x_1, x_2);
return x_3;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_Init_Data_Fin_Basic___instance__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_mod___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_div___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Fin_Init_Data_Fin_Basic___instance__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_modn___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
uint8_t l_Init_Data_Fin_Basic___instance__11___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Init_Data_Fin_Basic___instance__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Init_Data_Fin_Basic___instance__11___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Init_Data_Fin_Basic___instance__11___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Init_Data_Fin_Basic___instance__11___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Init_Data_Fin_Basic___instance__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Init_Data_Fin_Basic___instance__11(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Nat_Div(lean_object*);
lean_object* initialize_Init_Data_Nat_Bitwise(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Fin_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Div(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
