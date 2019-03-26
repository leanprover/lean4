// Lean compiler output
// Module: init.data.int.basic
// Imports: init.data.nat.basic init.data.list.default init.coe init.data.repr init.data.tostring
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Int_HasCoe(obj*);
namespace lean {
uint8 int_dec_nonneg(obj*);
}
obj* l_Int_negOfNat___main___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
namespace lean {
obj* nat2int(obj*);
}
namespace lean {
obj* int_sub(obj*, obj*);
}
extern usize l_String_toSubstring___closed__1;
obj* l_Int_HasDiv;
namespace lean {
obj* int_neg_succ_of_nat(obj*);
}
namespace lean {
uint8 int_dec_eq(obj*, obj*);
}
obj* l_Int_HasRepr;
obj* l_Int_negOfNat___boxed(obj*);
obj* l_Int_natMod(obj*, obj*);
obj* l_Int_repr___boxed(obj*);
obj* l_Int_toNat___main(obj*);
obj* l_Int_div___boxed(obj*, obj*);
obj* l___private_init_data_int_basic_2__decNonneg___boxed(obj*);
obj* l_Int_toNat___main___boxed(obj*);
namespace lean {
obj* int_neg(obj*);
}
obj* l_Int_HasMul;
obj* l_Int_neg___boxed(obj*);
obj* l_String_isInt___boxed(obj*);
obj* l_Int_HasToString;
obj* l_Int_add___boxed(obj*, obj*);
obj* l_Int_mod___boxed(obj*, obj*);
obj* l_Int_Int_DecidableEq;
obj* l_Int_HasAdd;
obj* l_Int_HasZero;
obj* l_Int_HasOne;
obj* l_Nat_repr(obj*);
obj* l_Int_HasMod;
usize l_String_toInt___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
namespace lean {
obj* int_add(obj*, obj*);
}
obj* l_Int_repr___main(obj*);
obj* l_Int_HasLess;
obj* l_Int_repr(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Int_sign(obj*);
obj* l_Int_natAbs___boxed(obj*);
uint8 l_String_isInt(obj*);
obj* l_Int_HasSub;
obj* l_Int_sign___main(obj*);
uint8 l_String_isInt___closed__1;
namespace lean {
uint32 string_utf8_get_old(obj*, usize);
}
obj* l_String_isInt___closed__1___boxed;
obj* l_String_toInt___closed__2;
obj* l_Int_decLt___boxed(obj*, obj*);
obj* l_Int_repr___main___closed__1;
obj* l_Int_HasNeg;
obj* l_Int_repr___main___closed__2;
namespace lean {
obj* int_mul(obj*, obj*);
}
uint8 l_String_isNat(obj*);
obj* l_Int_zero;
obj* l_Int_decLe___boxed(obj*, obj*);
obj* l_Int_negOfNat___main(obj*);
obj* l_Int_toNat(obj*);
obj* l_Substring_toNat(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_abs(obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_Int_subNatNat___boxed(obj*, obj*);
obj* l_Int_negOfNat(obj*);
obj* l_Int_sign___main___closed__1;
namespace lean {
usize string_utf8_byte_size_old(obj*);
}
obj* l_Int_decEq___boxed(obj*, obj*);
obj* l_Int_repr___main___boxed(obj*);
obj* l_Int_one;
obj* l_Int_toNat___boxed(obj*);
uint8 l_Substring_isNat(obj*);
obj* l_Int_subNatNat(obj*, obj*);
obj* l_Int_HasLessEq;
namespace lean {
uint8 int_dec_le(obj*, obj*);
}
obj* l_Int_natMod___boxed(obj*, obj*);
obj* l_String_toInt___closed__1___boxed;
obj* l_Int_sub___boxed(obj*, obj*);
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_Int_sign___main___boxed(obj*);
obj* l_String_toInt(obj*);
namespace lean {
obj* int_div(obj*, obj*);
}
obj* l_Int_sign___boxed(obj*);
namespace lean {
obj* int_mod(obj*, obj*);
}
obj* l_Int_mul___boxed(obj*, obj*);
obj* l_Int_HasCoe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_Int_zero() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_Int_one() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_Int_HasZero() {
_start:
{
obj* x_0; 
x_0 = l_Int_zero;
return x_0;
}
}
obj* _init_l_Int_HasOne() {
_start:
{
obj* x_0; 
x_0 = l_Int_one;
return x_0;
}
}
obj* l_Int_negOfNat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_0, x_3);
x_5 = lean::int_neg_succ_of_nat(x_4);
return x_5;
}
else
{
obj* x_6; 
x_6 = l_Int_zero;
return x_6;
}
}
}
obj* l_Int_negOfNat___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_negOfNat___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_negOfNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_negOfNat___main(x_0);
return x_1;
}
}
obj* l_Int_negOfNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_negOfNat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_neg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::int_neg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_subNatNat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::nat_sub(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
lean::dec(x_2);
x_8 = lean::int_neg_succ_of_nat(x_6);
return x_8;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_2);
x_10 = lean::nat_sub(x_0, x_1);
x_11 = lean::nat2int(x_10);
return x_11;
}
}
}
obj* l_Int_subNatNat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Int_subNatNat(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Int_add___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_add(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Int_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mul(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Int_HasNeg() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_neg___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Int_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Int_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_Int_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_sub(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Int_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Int_HasLessEq() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Int_HasLess() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_Int_decEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Int_Int_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_decEq___boxed), 2, 0);
return x_0;
}
}
obj* l___private_init_data_int_basic_2__decNonneg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::int_dec_nonneg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Int_decLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Int_decLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Int_natAbs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Int_repr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_Int_repr___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* l_Int_repr___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_Int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_abs(x_0);
x_4 = l_Nat_repr(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::nat_abs(x_0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_5, x_6);
lean::dec(x_5);
x_9 = lean::nat_add(x_7, x_6);
lean::dec(x_7);
x_11 = l_Nat_repr(x_9);
x_12 = l_Int_repr___main___closed__2;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
return x_13;
}
}
}
obj* l_Int_repr___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_repr___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_repr___main(x_0);
return x_1;
}
}
obj* l_Int_repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_repr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Int_HasRepr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_repr___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Int_HasToString() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_repr___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Int_sign___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Int_one;
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* l_Int_sign___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_Int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::nat_abs(x_0);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_7; 
x_7 = l_Int_one;
return x_7;
}
else
{
obj* x_8; 
x_8 = l_Int_zero;
return x_8;
}
}
else
{
obj* x_9; 
x_9 = l_Int_sign___main___closed__1;
return x_9;
}
}
}
obj* l_Int_sign___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_sign___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_sign(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_sign___main(x_0);
return x_1;
}
}
obj* l_Int_sign___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_sign(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_div___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_div(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Int_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mod(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Int_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Int_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Int_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_Int_toNat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_Int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; 
x_3 = lean::nat_abs(x_0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
}
}
obj* l_Int_toNat___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_toNat___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_toNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_toNat___main(x_0);
return x_1;
}
}
obj* l_Int_toNat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Int_toNat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Int_natMod(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::int_mod(x_0, x_1);
x_3 = l_Int_toNat___main(x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Int_natMod___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Int_natMod(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
usize _init_l_String_toInt___closed__1() {
_start:
{
obj* x_0; usize x_1; obj* x_2; usize x_3; usize x_4; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::usize_of_nat(x_2);
x_4 = x_1 + x_3;
return x_4;
}
}
obj* _init_l_String_toInt___closed__2() {
_start:
{
obj* x_0; usize x_1; obj* x_2; usize x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::mk_string("");
x_3 = lean::string_utf8_byte_size_old(x_2);
x_4 = lean::alloc_cnstr(0, 1, sizeof(size_t)*2);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_1);
x_5 = x_4;
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
x_6 = x_5;
x_7 = l_Substring_toNat(x_6);
lean::dec(x_6);
x_9 = lean::nat2int(x_7);
x_10 = lean::int_neg(x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_String_toInt(obj* x_0) {
_start:
{
usize x_1; uint32 x_2; uint32 x_3; uint8 x_4; 
x_1 = l_String_toSubstring___closed__1;
x_2 = lean::string_utf8_get_old(x_0, x_1);
x_3 = 45;
x_4 = x_2 == x_3;
if (x_4 == 0)
{
obj* x_5; obj* x_7; 
x_5 = l_String_toNat(x_0);
lean::dec(x_0);
x_7 = lean::nat2int(x_5);
return x_7;
}
else
{
usize x_8; usize x_9; uint8 x_10; 
x_8 = lean::string_utf8_byte_size_old(x_0);
x_9 = l_String_toInt___closed__1;
x_10 = x_8 <= x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_11 = lean::alloc_cnstr(0, 1, sizeof(size_t)*2);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_9);
x_12 = x_11;
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_8);
x_13 = x_12;
x_14 = l_Substring_toNat(x_13);
lean::dec(x_13);
x_16 = lean::nat2int(x_14);
x_17 = lean::int_neg(x_16);
lean::dec(x_16);
return x_17;
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l_String_toInt___closed__2;
return x_20;
}
}
}
}
obj* _init_l_String_toInt___closed__1___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_String_toInt___closed__1;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
uint8 _init_l_String_isInt___closed__1() {
_start:
{
obj* x_0; usize x_1; obj* x_2; usize x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::mk_string("");
x_3 = lean::string_utf8_byte_size_old(x_2);
x_4 = lean::alloc_cnstr(0, 1, sizeof(size_t)*2);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_1);
x_5 = x_4;
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
x_6 = x_5;
x_7 = l_Substring_isNat(x_6);
lean::dec(x_6);
return x_7;
}
}
uint8 l_String_isInt(obj* x_0) {
_start:
{
usize x_1; uint32 x_2; uint32 x_3; uint8 x_4; 
x_1 = l_String_toSubstring___closed__1;
x_2 = lean::string_utf8_get_old(x_0, x_1);
x_3 = 45;
x_4 = x_2 == x_3;
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_isNat(x_0);
lean::dec(x_0);
return x_5;
}
else
{
usize x_7; usize x_8; uint8 x_9; 
x_7 = lean::string_utf8_byte_size_old(x_0);
x_8 = l_String_toInt___closed__1;
x_9 = x_7 <= x_8;
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_10 = lean::alloc_cnstr(0, 1, sizeof(size_t)*2);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set_scalar(x_10, sizeof(void*)*1, x_8);
x_11 = x_10;
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_7);
x_12 = x_11;
x_13 = l_Substring_isNat(x_12);
lean::dec(x_12);
return x_13;
}
else
{
uint8 x_16; 
lean::dec(x_0);
x_16 = l_String_isInt___closed__1;
return x_16;
}
}
}
}
obj* _init_l_String_isInt___closed__1___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_String_isInt___closed__1;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_String_isInt___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_String_isInt(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_list_default(obj*);
obj* initialize_init_coe(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_int_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
 l_Int_zero = _init_l_Int_zero();
lean::mark_persistent(l_Int_zero);
 l_Int_one = _init_l_Int_one();
lean::mark_persistent(l_Int_one);
 l_Int_HasZero = _init_l_Int_HasZero();
lean::mark_persistent(l_Int_HasZero);
 l_Int_HasOne = _init_l_Int_HasOne();
lean::mark_persistent(l_Int_HasOne);
 l_Int_HasNeg = _init_l_Int_HasNeg();
lean::mark_persistent(l_Int_HasNeg);
 l_Int_HasAdd = _init_l_Int_HasAdd();
lean::mark_persistent(l_Int_HasAdd);
 l_Int_HasMul = _init_l_Int_HasMul();
lean::mark_persistent(l_Int_HasMul);
 l_Int_HasSub = _init_l_Int_HasSub();
lean::mark_persistent(l_Int_HasSub);
 l_Int_HasLessEq = _init_l_Int_HasLessEq();
lean::mark_persistent(l_Int_HasLessEq);
 l_Int_HasLess = _init_l_Int_HasLess();
lean::mark_persistent(l_Int_HasLess);
 l_Int_Int_DecidableEq = _init_l_Int_Int_DecidableEq();
lean::mark_persistent(l_Int_Int_DecidableEq);
 l_Int_repr___main___closed__1 = _init_l_Int_repr___main___closed__1();
lean::mark_persistent(l_Int_repr___main___closed__1);
 l_Int_repr___main___closed__2 = _init_l_Int_repr___main___closed__2();
lean::mark_persistent(l_Int_repr___main___closed__2);
 l_Int_HasRepr = _init_l_Int_HasRepr();
lean::mark_persistent(l_Int_HasRepr);
 l_Int_HasToString = _init_l_Int_HasToString();
lean::mark_persistent(l_Int_HasToString);
 l_Int_sign___main___closed__1 = _init_l_Int_sign___main___closed__1();
lean::mark_persistent(l_Int_sign___main___closed__1);
 l_Int_HasDiv = _init_l_Int_HasDiv();
lean::mark_persistent(l_Int_HasDiv);
 l_Int_HasMod = _init_l_Int_HasMod();
lean::mark_persistent(l_Int_HasMod);
 l_String_toInt___closed__1 = _init_l_String_toInt___closed__1();
 l_String_toInt___closed__2 = _init_l_String_toInt___closed__2();
lean::mark_persistent(l_String_toInt___closed__2);
 l_String_toInt___closed__1___boxed = _init_l_String_toInt___closed__1___boxed();
lean::mark_persistent(l_String_toInt___closed__1___boxed);
 l_String_isInt___closed__1 = _init_l_String_isInt___closed__1();
 l_String_isInt___closed__1___boxed = _init_l_String_isInt___closed__1___boxed();
lean::mark_persistent(l_String_isInt___closed__1___boxed);
return w;
}
