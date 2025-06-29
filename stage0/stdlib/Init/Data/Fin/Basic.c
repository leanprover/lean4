// Lean compiler output
// Module: Init.Data.Fin.Basic
// Imports: Init.Data.Nat.Bitwise.Basic
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
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object*);
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_last(lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_xor(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instXor(lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_lor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_mod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_land(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_coeToNat___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_coeToNat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_coeToNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_coeToNat(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_elim0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Fin_elim0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_elim0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_succ(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_succ___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_succ___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_succ___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_succ(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_ofNat___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_ofNat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_ofNat_x27___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_ofNat_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_ofNat_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_toNat___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_toNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_toNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_add(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_mul(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_mul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_sub(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_nat_sub(x_1, x_3);
x_5 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_6 = lean_nat_mod(x_5, x_1);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_sub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_mod___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_mod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_mod___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_mod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_div___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_div(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_div(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_div___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_div___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_div___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_modn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_modn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_modn___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_modn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Fin_land(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_land(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_land___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_land(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_lor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_lor(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_lor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_lor(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_xor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_lxor(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_xor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_xor(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_shiftl(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_shiftLeft(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_shiftr(x_2, x_3);
x_5 = lean_nat_mod(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_shiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_shiftRight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_add___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instSub(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_sub___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instMul(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_mul___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instMod(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_mod___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instDiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_div___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instAndOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_land___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instOrOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_lor___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instXor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_xor___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_shiftLeft___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instShiftRight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_shiftRight___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_mod(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instOfNat___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instOfNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_instOfNat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_sub(x_1, x_2);
x_4 = lean_nat_mod(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_neg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_neg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_neg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_neg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instInhabited___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_instInhabited___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_instInhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_instInhabited(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_3(x_3, x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_5, x_3, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Fin_last(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_last___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_last(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_castLT___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Fin_castLT(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_castLE___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Fin_castLE(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_cast___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Fin_cast(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_castAdd___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_castAdd(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_castSucc___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_castSucc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_castSucc(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_addNat___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_addNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_addNat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_natAdd___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_natAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_natAdd(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_rev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_rev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_sub(x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Fin_subNat___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_subNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Fin_subNat(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Fin_pred(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_pred___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_pred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_pred(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
