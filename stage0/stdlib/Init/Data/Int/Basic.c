// Lean compiler output
// Module: Init.Data.Int.Basic
// Imports: Init.Data.Nat.Basic Init.Data.List Init.Data.Repr Init.Data.ToString.Basic
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
extern lean_object* l___kind_term____x40_Init_Notation___hyg_2503____closed__2;
lean_object* l_Int_instNegInt___closed__1;
uint8_t l_String_isInt(lean_object*);
lean_object* l_Int_instAddInt___closed__1;
lean_object* l_Int_toNat_match__1(lean_object*);
lean_object* l_Int_instNegInt;
lean_object* l_Int_natMod(lean_object*, lean_object*);
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_String_toInt_x21___closed__1;
lean_object* l_Substring_toNat_x3f(lean_object*);
lean_object* l_String_isInt___boxed(lean_object*);
lean_object* l_String_toInt_x21___closed__2;
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
uint8_t l_Int_instDecidableEqInt(lean_object*, lean_object*);
lean_object* l_Int_negSucc___boxed(lean_object*);
lean_object* l_String_toInt_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Int_Int_pow_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_mod_match__1(lean_object*);
lean_object* l_String_toInt_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_toInt_x21(lean_object*);
lean_object* l_Int_instMulInt___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_Int_pow___closed__1;
lean_object* l_Int_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Int_mod_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Int_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Int_repr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Int_instSubInt;
lean_object* l_Int_mod_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_instDivInt;
lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
lean_object* l_Int_instDivInt___closed__1;
lean_object* l_Int_div___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Int_Basic_0__Int_decNonneg___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_negOfNat_match__1(lean_object*);
lean_object* l_Int_instDecidableEqInt___boxed(lean_object*, lean_object*);
uint8_t l_Substring_isNat(lean_object*);
lean_object* l_Int_subNatNat_match__1(lean_object*);
lean_object* l_Int_instSubInt___closed__1;
lean_object* l_Int_negOfNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_div_match__1(lean_object*);
lean_object* l_Int_instHPowIntNatInt;
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* l_Int_instModInt;
lean_object* l_Int_toNat___boxed(lean_object*);
lean_object* l_Int_mod___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* l_Int_Int_pow_match__1(lean_object*);
lean_object* l_Int_div_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l_Int_instInhabitedInt;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_toInt_x21_match__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instModInt___closed__1;
lean_object* l_Int_negOfNat___boxed(lean_object*);
lean_object* l_Int_Int_pow_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_negOfNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instHasLessEqInt;
lean_object* l_Int_natMod___boxed(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Int_toNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instToStringInt;
lean_object* lean_int_neg(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_instCoeNatInt(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* l_Int_Int_pow___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* l_Int_instOfNatInt(lean_object*);
lean_object* l_Int_subNatNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Int_div_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_subNatNat___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* l_Int_subNatNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Int_repr_match__1(lean_object*);
lean_object* l_Int_instHasLessInt;
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_String_toInt_x21___closed__4;
lean_object* l_Int_instReprInt;
lean_object* l_Int_instReprInt___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
lean_object* l_Int_natAbs___boxed(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_instHPowIntNatInt___closed__1;
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_String_toInt_x21___closed__3;
lean_object* l_Int_instMulInt;
lean_object* l_Int_Int_pow(lean_object*, lean_object*);
lean_object* l_Int_instAddInt;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_negSucc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
lean_object* l_instCoeNatInt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instInhabitedInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instInhabitedInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instInhabitedInt___closed__1;
return x_1;
}
}
lean_object* l_Int_negOfNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Int_negOfNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_negOfNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_negOfNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_negOfNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_negOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_int_neg_succ_of_nat(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Int_instInhabitedInt___closed__1;
return x_7;
}
}
}
lean_object* l_Int_negOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_negOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_neg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_subNatNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Int_subNatNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_subNatNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_subNatNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_subNatNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_subNatNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_nat_sub(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_int_neg_succ_of_nat(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_nat_sub(x_1, x_2);
x_10 = lean_nat_to_int(x_9);
return x_10;
}
}
}
lean_object* l_Int_subNatNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_subNatNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instNegInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_neg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instNegInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instNegInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instAddInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instAddInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instAddInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instMulInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instMulInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instMulInt___closed__1;
return x_1;
}
}
lean_object* l_Int_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instSubInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instSubInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instSubInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instHasLessEqInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Int_instHasLessInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Int_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Int_instDecidableEqInt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Int_instDecidableEqInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_instDecidableEqInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_Int_Basic_0__Int_decNonneg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_int_dec_nonneg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Int_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_le(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Int_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Int_natAbs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_abs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_repr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_instInhabitedInt___closed__1;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
lean_object* l_Int_repr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_repr_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_repr_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_repr_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabitedInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_repr(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = l_Nat_repr(x_9);
x_11 = l___kind_term____x40_Init_Notation___hyg_2503____closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_Int_repr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_repr(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instReprInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_repr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instReprInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instReprInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instToStringInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instReprInt___closed__1;
return x_1;
}
}
lean_object* l_Int_instOfNatInt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_div_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Int_instInhabitedInt___closed__1;
x_8 = lean_int_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_nat_abs(x_1);
x_10 = lean_int_dec_lt(x_2, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_nat_abs(x_2);
x_12 = lean_apply_2(x_3, x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_nat_abs(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_apply_2(x_4, x_9, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_nat_abs(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_int_dec_lt(x_2, x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_nat_abs(x_2);
x_22 = lean_apply_2(x_5, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_23 = lean_nat_abs(x_2);
x_24 = lean_nat_sub(x_23, x_18);
lean_dec(x_23);
x_25 = lean_apply_2(x_6, x_19, x_24);
return x_25;
}
}
}
}
lean_object* l_Int_div_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_div_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Int_div_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_div_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Int_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_mod_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Int_instInhabitedInt___closed__1;
x_8 = lean_int_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_nat_abs(x_1);
x_10 = lean_int_dec_lt(x_2, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_nat_abs(x_2);
x_12 = lean_apply_2(x_3, x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_nat_abs(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_apply_2(x_4, x_9, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_nat_abs(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_int_dec_lt(x_2, x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_nat_abs(x_2);
x_22 = lean_apply_2(x_5, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_23 = lean_nat_abs(x_2);
x_24 = lean_nat_sub(x_23, x_18);
lean_dec(x_23);
x_25 = lean_apply_2(x_6, x_19, x_24);
return x_25;
}
}
}
}
lean_object* l_Int_mod_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_mod_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Int_mod_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_mod_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Int_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instDivInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instDivInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instDivInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instModInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instModInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instModInt___closed__1;
return x_1;
}
}
lean_object* l_Int_toNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_instInhabitedInt___closed__1;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
lean_object* l_Int_toNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_toNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_toNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_toNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabitedInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_nat_abs(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
}
lean_object* l_Int_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_natMod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_int_mod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Int_natMod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_natMod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_Int_pow_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Int_Int_pow_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_Int_pow_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_Int_pow_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Int_pow_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Int_Int_pow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_Int_pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Int_Int_pow(x_1, x_6);
lean_dec(x_6);
x_8 = lean_int_mul(x_7, x_1);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Int_Int_pow___closed__1;
return x_9;
}
}
}
lean_object* l_Int_Int_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Int_pow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instHPowIntNatInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Int_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instHPowIntNatInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instHPowIntNatInt___closed__1;
return x_1;
}
}
lean_object* l_String_toInt_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_String_toNat_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_nat_to_int(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_string_utf8_byte_size(x_1);
lean_inc(x_14);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Substring_nextn(x_15, x_16, x_2);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
x_19 = l_Substring_toNat_x3f(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_neg(x_23);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_neg(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_String_isNat(x_1);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_string_utf8_byte_size(x_1);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Substring_nextn(x_8, x_9, x_2);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_7);
x_12 = l_Substring_isNat(x_11);
return x_12;
}
}
}
lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_String_toInt_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_String_toInt_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_toInt_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_String_toInt_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Int.Basic");
return x_1;
}
}
static lean_object* _init_l_String_toInt_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String.toInt!");
return x_1;
}
}
static lean_object* _init_l_String_toInt_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Int expected");
return x_1;
}
}
static lean_object* _init_l_String_toInt_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_String_toInt_x21___closed__1;
x_2 = l_String_toInt_x21___closed__2;
x_3 = lean_unsigned_to_nat(193u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_String_toInt_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_String_toInt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toInt_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Int_instInhabitedInt;
x_4 = l_String_toInt_x21___closed__4;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
lean_object* initialize_Init_Data_List(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Int_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instInhabitedInt___closed__1 = _init_l_Int_instInhabitedInt___closed__1();
lean_mark_persistent(l_Int_instInhabitedInt___closed__1);
l_Int_instInhabitedInt = _init_l_Int_instInhabitedInt();
lean_mark_persistent(l_Int_instInhabitedInt);
l_Int_instNegInt___closed__1 = _init_l_Int_instNegInt___closed__1();
lean_mark_persistent(l_Int_instNegInt___closed__1);
l_Int_instNegInt = _init_l_Int_instNegInt();
lean_mark_persistent(l_Int_instNegInt);
l_Int_instAddInt___closed__1 = _init_l_Int_instAddInt___closed__1();
lean_mark_persistent(l_Int_instAddInt___closed__1);
l_Int_instAddInt = _init_l_Int_instAddInt();
lean_mark_persistent(l_Int_instAddInt);
l_Int_instMulInt___closed__1 = _init_l_Int_instMulInt___closed__1();
lean_mark_persistent(l_Int_instMulInt___closed__1);
l_Int_instMulInt = _init_l_Int_instMulInt();
lean_mark_persistent(l_Int_instMulInt);
l_Int_instSubInt___closed__1 = _init_l_Int_instSubInt___closed__1();
lean_mark_persistent(l_Int_instSubInt___closed__1);
l_Int_instSubInt = _init_l_Int_instSubInt();
lean_mark_persistent(l_Int_instSubInt);
l_Int_instHasLessEqInt = _init_l_Int_instHasLessEqInt();
lean_mark_persistent(l_Int_instHasLessEqInt);
l_Int_instHasLessInt = _init_l_Int_instHasLessInt();
lean_mark_persistent(l_Int_instHasLessInt);
l_Int_instReprInt___closed__1 = _init_l_Int_instReprInt___closed__1();
lean_mark_persistent(l_Int_instReprInt___closed__1);
l_Int_instReprInt = _init_l_Int_instReprInt();
lean_mark_persistent(l_Int_instReprInt);
l_Int_instToStringInt = _init_l_Int_instToStringInt();
lean_mark_persistent(l_Int_instToStringInt);
l_Int_instDivInt___closed__1 = _init_l_Int_instDivInt___closed__1();
lean_mark_persistent(l_Int_instDivInt___closed__1);
l_Int_instDivInt = _init_l_Int_instDivInt();
lean_mark_persistent(l_Int_instDivInt);
l_Int_instModInt___closed__1 = _init_l_Int_instModInt___closed__1();
lean_mark_persistent(l_Int_instModInt___closed__1);
l_Int_instModInt = _init_l_Int_instModInt();
lean_mark_persistent(l_Int_instModInt);
l_Int_Int_pow___closed__1 = _init_l_Int_Int_pow___closed__1();
lean_mark_persistent(l_Int_Int_pow___closed__1);
l_Int_instHPowIntNatInt___closed__1 = _init_l_Int_instHPowIntNatInt___closed__1();
lean_mark_persistent(l_Int_instHPowIntNatInt___closed__1);
l_Int_instHPowIntNatInt = _init_l_Int_instHPowIntNatInt();
lean_mark_persistent(l_Int_instHPowIntNatInt);
l_String_toInt_x21___closed__1 = _init_l_String_toInt_x21___closed__1();
lean_mark_persistent(l_String_toInt_x21___closed__1);
l_String_toInt_x21___closed__2 = _init_l_String_toInt_x21___closed__2();
lean_mark_persistent(l_String_toInt_x21___closed__2);
l_String_toInt_x21___closed__3 = _init_l_String_toInt_x21___closed__3();
lean_mark_persistent(l_String_toInt_x21___closed__3);
l_String_toInt_x21___closed__4 = _init_l_String_toInt_x21___closed__4();
lean_mark_persistent(l_String_toInt_x21___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
