// Lean compiler output
// Module: init.data.int.basic
// Imports: init.data.nat.basic init.data.list.default init.coe init.data.repr init.data.to_string
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
obj* l_int_repr(obj*);
obj* l_int_has__repr;
namespace lean {
obj* nat_abs(obj*);
}
namespace lean {
obj* nat2int(obj*);
}
obj* l_int_neg__of__nat(obj*);
namespace lean {
uint8 int_dec_nonneg(obj*);
}
obj* l_int_has__sub;
namespace lean {
obj* int_neg_succ_of_nat(obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_int_add___boxed(obj*, obj*);
namespace lean {
uint8 int_dec_le(obj*, obj*);
}
obj* l_int_neg___boxed(obj*);
obj* l_int_repr___main(obj*);
obj* l_int_div___boxed(obj*, obj*);
namespace lean {
obj* int_mod(obj*, obj*);
}
obj* l_int_to__nat___main(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_int_sub___boxed(obj*, obj*);
obj* l_int_has__mul;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_int_lt;
obj* l_int_neg__of__nat___main(obj*);
obj* l_int_has__lt;
obj* l_int_int_decidable__eq;
obj* l_int_nat__abs___boxed(obj*);
obj* l_int_sub__nat__nat(obj*, obj*);
obj* l_int_dec__lt___boxed(obj*, obj*);
namespace lean {
obj* int_add(obj*, obj*);
}
obj* l_int_zero;
obj* l_int_has__div;
namespace lean {
obj* int_sub(obj*, obj*);
}
obj* l_int_has__mod;
obj* l_int_sign(obj*);
obj* l_int_repr___main___closed__1;
obj* l_int_to__nat(obj*);
obj* l_int_dec__eq___boxed(obj*, obj*);
obj* l_int_has__coe(obj*);
obj* l_int_has__le;
obj* l_int_has__one;
namespace lean {
obj* int_div(obj*, obj*);
}
obj* l_int_nat__mod(obj*, obj*);
obj* l_int_mod___boxed(obj*, obj*);
obj* l___private_init_data_int_basic_2__dec__nonneg___boxed(obj*);
obj* l_int_has__neg;
obj* l___private_init_data_int_basic_1__nonneg;
namespace lean {
obj* int_neg(obj*);
}
obj* l_int_repr___main___closed__2;
obj* l_int_has__to__string;
obj* l_nat_repr(obj*);
obj* l___private_init_data_int_basic_1__nonneg___main;
obj* l_int_mul___boxed(obj*, obj*);
obj* l_int_sign___main(obj*);
obj* l_int_has__add;
obj* l_int_le;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_int_has__zero;
obj* l_int_dec__le___boxed(obj*, obj*);
obj* l_int_sign___main___closed__1;
namespace lean {
obj* int_mul(obj*, obj*);
}
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_int_one;
namespace lean {
uint8 int_dec_eq(obj*, obj*);
}
obj* l_int_has__coe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_zero() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_one() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_has__zero() {
_start:
{
obj* x_0; 
x_0 = l_int_zero;
return x_0;
}
}
obj* _init_l_int_has__one() {
_start:
{
obj* x_0; 
x_0 = l_int_one;
return x_0;
}
}
obj* _init_l___private_init_data_int_basic_1__nonneg___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l___private_init_data_int_basic_1__nonneg() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_int_neg__of__nat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_6; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_0, x_3);
lean::dec(x_0);
x_6 = lean::int_neg_succ_of_nat(x_4);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_0);
x_8 = l_int_zero;
return x_8;
}
}
}
obj* l_int_neg__of__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_neg__of__nat___main(x_0);
return x_1;
}
}
obj* l_int_neg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* l_int_sub__nat__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::nat_sub(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_7; obj* x_8; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::int_neg_succ_of_nat(x_8);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
lean::dec(x_2);
x_12 = lean::nat_sub(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::nat2int(x_12);
return x_15;
}
}
}
obj* l_int_add___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_add(x_0, x_1);
return x_2;
}
}
obj* l_int_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mul(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__neg() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_neg___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_int_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_int_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_sub(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_int_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_int_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_int_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_int_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_int_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_int_int_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l___private_init_data_int_basic_2__dec__nonneg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::int_dec_nonneg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_int_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_int_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_int_nat__abs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat_abs(x_0);
return x_1;
}
}
obj* _init_l_int_repr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_repr___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* l_int_repr___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = l_nat_repr(x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_6 = lean::nat_abs(x_0);
lean::dec(x_0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_6, x_8);
lean::dec(x_6);
x_11 = lean::nat_add(x_9, x_8);
lean::dec(x_9);
x_13 = l_nat_repr(x_11);
x_14 = l_int_repr___main___closed__2;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
return x_15;
}
}
}
obj* l_int_repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_repr___main(x_0);
return x_1;
}
}
obj* _init_l_int_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_repr), 1, 0);
return x_0;
}
}
obj* _init_l_int_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_repr), 1, 0);
return x_0;
}
}
obj* _init_l_int_sign___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_int_one;
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* l_int_sign___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; uint8 x_6; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
lean::dec(x_3);
if (x_6 == 0)
{
obj* x_8; 
x_8 = l_int_one;
return x_8;
}
else
{
obj* x_9; 
x_9 = l_int_zero;
return x_9;
}
}
else
{
obj* x_11; 
lean::dec(x_0);
x_11 = l_int_sign___main___closed__1;
return x_11;
}
}
}
obj* l_int_sign(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_sign___main(x_0);
return x_1;
}
}
obj* l_int_div___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_div(x_0, x_1);
return x_2;
}
}
obj* l_int_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mod(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_int_to__nat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_3;
}
else
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
}
}
obj* l_int_to__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_to__nat___main(x_0);
return x_1;
}
}
obj* l_int_nat__mod(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::int_mod(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_int_to__nat___main(x_2);
return x_5;
}
}
void initialize_init_data_nat_basic();
void initialize_init_data_list_default();
void initialize_init_coe();
void initialize_init_data_repr();
void initialize_init_data_to__string();
static bool _G_initialized = false;
void initialize_init_data_int_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 initialize_init_data_list_default();
 initialize_init_coe();
 initialize_init_data_repr();
 initialize_init_data_to__string();
 l_int_zero = _init_l_int_zero();
lean::mark_persistent(l_int_zero);
 l_int_one = _init_l_int_one();
lean::mark_persistent(l_int_one);
 l_int_has__zero = _init_l_int_has__zero();
lean::mark_persistent(l_int_has__zero);
 l_int_has__one = _init_l_int_has__one();
lean::mark_persistent(l_int_has__one);
 l___private_init_data_int_basic_1__nonneg___main = _init_l___private_init_data_int_basic_1__nonneg___main();
lean::mark_persistent(l___private_init_data_int_basic_1__nonneg___main);
 l___private_init_data_int_basic_1__nonneg = _init_l___private_init_data_int_basic_1__nonneg();
lean::mark_persistent(l___private_init_data_int_basic_1__nonneg);
 l_int_has__neg = _init_l_int_has__neg();
lean::mark_persistent(l_int_has__neg);
 l_int_has__add = _init_l_int_has__add();
lean::mark_persistent(l_int_has__add);
 l_int_has__mul = _init_l_int_has__mul();
lean::mark_persistent(l_int_has__mul);
 l_int_has__sub = _init_l_int_has__sub();
lean::mark_persistent(l_int_has__sub);
 l_int_le = _init_l_int_le();
lean::mark_persistent(l_int_le);
 l_int_has__le = _init_l_int_has__le();
lean::mark_persistent(l_int_has__le);
 l_int_lt = _init_l_int_lt();
lean::mark_persistent(l_int_lt);
 l_int_has__lt = _init_l_int_has__lt();
lean::mark_persistent(l_int_has__lt);
 l_int_int_decidable__eq = _init_l_int_int_decidable__eq();
lean::mark_persistent(l_int_int_decidable__eq);
 l_int_repr___main___closed__1 = _init_l_int_repr___main___closed__1();
lean::mark_persistent(l_int_repr___main___closed__1);
 l_int_repr___main___closed__2 = _init_l_int_repr___main___closed__2();
lean::mark_persistent(l_int_repr___main___closed__2);
 l_int_has__repr = _init_l_int_has__repr();
lean::mark_persistent(l_int_has__repr);
 l_int_has__to__string = _init_l_int_has__to__string();
lean::mark_persistent(l_int_has__to__string);
 l_int_sign___main___closed__1 = _init_l_int_sign___main___closed__1();
lean::mark_persistent(l_int_sign___main___closed__1);
 l_int_has__div = _init_l_int_has__div();
lean::mark_persistent(l_int_has__div);
 l_int_has__mod = _init_l_int_has__mod();
lean::mark_persistent(l_int_has__mod);
}
