// Lean compiler output
// Module: init.data.uint
// Imports: init.data.fin.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_uint32_has__le;
obj* l_uint8_has__div;
obj* l_uint64_sub___boxed(obj*, obj*);
unsigned char l_uint8_inhabited;
obj* l_uint16_sub___boxed(obj*, obj*);
obj* l_uint16_le;
obj* l_uint8_mul___boxed(obj*, obj*);
obj* l_uint16_dec__le___boxed(obj*, obj*);
obj* l_uint32_has__decidable__lt(unsigned, unsigned);
obj* l_uint8_has__modn;
obj* l_uint32_lt;
obj* l_uint16_has__decidable__lt(unsigned short, unsigned short);
obj* l_uint8_decidable__eq;
unsigned long long l_uint64_has__one;
obj* l_uint32_has__decidable__le(unsigned, unsigned);
obj* l_uint16_mul___boxed(obj*, obj*);
obj* l_uint16_dec__lt___boxed(obj*, obj*);
obj* l_uint8__sz;
obj* l_uint16_has__lt;
obj* l_uint64_has__lt;
obj* l_uint16_has__mod;
obj* l_uint64_decidable__eq;
obj* l_uint16_mod___boxed(obj*, obj*);
obj* l_uint64_has__add;
obj* l_uint32_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint8_mod___boxed(obj*, obj*);
obj* l_uint16_lt;
obj* l_uint32__sz;
obj* l_uint32_dec__le___boxed(obj*, obj*);
obj* l_uint32_add___boxed(obj*, obj*);
unsigned long long l_uint64_inhabited;
obj* l_uint16_to__nat___boxed(obj*);
obj* l_uint32_inhabited___boxed;
obj* l_uint64_has__div;
obj* l_uint8_add___boxed(obj*, obj*);
obj* l_uint16_has__div;
obj* l_uint64_has__sub;
obj* l_uint64_has__mod;
obj* l_uint32_div___boxed(obj*, obj*);
obj* l_uint32_of__nat___boxed(obj*);
obj* l_uint16_has__decidable__le___boxed(obj*, obj*);
obj* l_uint64_has__decidable__le___boxed(obj*, obj*);
obj* l_uint8_dec__lt___boxed(obj*, obj*);
obj* l_uint32_has__lt;
obj* l_uint32_has__sub;
obj* l_uint64_mul___boxed(obj*, obj*);
obj* l_uint16_has__add;
obj* l_uint64_has__modn;
obj* l_uint64_dec__lt___boxed(obj*, obj*);
obj* l_uint32_dec__eq___boxed(obj*, obj*);
obj* l_uint16_has__mul;
obj* l_uint8_has__decidable__le___boxed(obj*, obj*);
obj* l_uint64_lt;
obj* l_uint64_has__decidable__le(unsigned long long, unsigned long long);
obj* l_uint16_inhabited___boxed;
obj* l_uint64__sz;
obj* l_uint64_mod___boxed(obj*, obj*);
obj* l_uint32_le;
obj* l_uint8_has__decidable__le(unsigned char, unsigned char);
obj* l_uint16_dec__eq___boxed(obj*, obj*);
obj* l_uint8_lt;
obj* l_uint32_modn___boxed(obj*, obj*);
obj* l_uint32_has__mod;
obj* l_uint8_div___boxed(obj*, obj*);
unsigned l_uint32_inhabited;
obj* l_uint32_sub___boxed(obj*, obj*);
obj* l_uint32_has__div;
obj* l_uint8_dec__le___boxed(obj*, obj*);
obj* l_uint8_has__decidable__lt___boxed(obj*, obj*);
unsigned short l_uint16_has__zero;
obj* l_uint16_has__decidable__le(unsigned short, unsigned short);
obj* l_uint8_dec__eq___boxed(obj*, obj*);
obj* l_uint16_decidable__eq;
obj* l_uint8_has__add;
obj* l_uint32_decidable__eq;
obj* l_uint8_has__one___boxed;
obj* l_uint64_has__one___boxed;
obj* l_uint64_has__mul;
unsigned short l_uint16_has__one;
obj* l_uint8_sub___boxed(obj*, obj*);
obj* l_uint64_has__zero___boxed;
obj* l_uint64_of__nat___boxed(obj*);
obj* l_uint64_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint16_has__one___boxed;
obj* l_uint32_has__zero___boxed;
obj* l_uint16__sz;
obj* l_uint64_add___boxed(obj*, obj*);
unsigned char l_uint8_has__one;
obj* l_uint64_le;
obj* l_uint8_has__zero___boxed;
obj* l_uint8_has__decidable__lt(unsigned char, unsigned char);
obj* l_uint32_has__decidable__le___boxed(obj*, obj*);
obj* l_uint8_has__mod;
obj* l_uint64_has__le;
obj* l_uint8_le;
obj* l_uint64_div___boxed(obj*, obj*);
obj* l_uint16_div___boxed(obj*, obj*);
obj* l_uint8_has__lt;
obj* l_uint64_inhabited___boxed;
obj* l_uint64_has__decidable__lt(unsigned long long, unsigned long long);
obj* l_uint16_has__modn;
obj* l_uint32_mod___boxed(obj*, obj*);
obj* l_uint16_modn___boxed(obj*, obj*);
obj* l_uint32_dec__lt___boxed(obj*, obj*);
obj* l_uint16_has__zero___boxed;
obj* l_uint32_has__one___boxed;
obj* l_uint8_has__le;
obj* l_uint16_of__nat___boxed(obj*);
obj* l_uint64_dec__le___boxed(obj*, obj*);
obj* l_uint64_modn___boxed(obj*, obj*);
obj* l_uint16_has__le;
obj* l_uint8_to__nat___boxed(obj*);
obj* l_uint8_has__mul;
obj* l_uint16_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint32_has__modn;
obj* l_uint8_has__sub;
obj* l_uint8_of__nat___boxed(obj*);
obj* l_uint32_to__nat___boxed(obj*);
unsigned l_uint32_has__one;
obj* l_uint32_mul___boxed(obj*, obj*);
obj* l_uint16_has__sub;
obj* l_uint8_modn___boxed(obj*, obj*);
obj* l_uint64_to__nat___boxed(obj*);
obj* l_uint16_add___boxed(obj*, obj*);
unsigned char l_uint8_has__zero;
obj* l_uint64_dec__eq___boxed(obj*, obj*);
unsigned l_uint32_has__zero;
unsigned short l_uint16_inhabited;
obj* l_uint32_has__mul;
unsigned long long l_uint64_has__zero;
obj* l_uint32_has__add;
obj* l_uint8_inhabited___boxed;
obj* _init_l_uint8__sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(256u);
return x_0;
}
}
obj* l_uint8_of__nat___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::uint8_of_nat(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_uint8_to__nat___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint8_to_nat(x_1);
return x_2;
}
}
obj* l_uint8_add___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_add(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_sub(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_mul(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_div___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_div(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_mod(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::uint8_modn(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_uint8_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_uint8_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned char _init_l_uint8_has__zero() {
_start:
{
obj* x_0; unsigned char x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint8_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint8_has__zero___boxed() {
_start:
{
unsigned char x_0; obj* x_1; 
x_0 = l_uint8_has__zero;
x_1 = lean::box(x_0);
return x_1;
}
}
unsigned char _init_l_uint8_has__one() {
_start:
{
obj* x_0; unsigned char x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint8_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint8_has__one___boxed() {
_start:
{
unsigned char x_0; obj* x_1; 
x_0 = l_uint8_has__one;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_uint8_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint8_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init_l_uint8_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
unsigned char _init_l_uint8_inhabited() {
_start:
{
obj* x_0; unsigned char x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint8_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint8_inhabited___boxed() {
_start:
{
unsigned char x_0; obj* x_1; 
x_0 = l_uint8_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_uint8_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_uint8_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_dec_lt(x_2, x_3);
return x_4;
}
}
obj* l_uint8_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint8_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint8_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint8_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_uint8_has__decidable__lt(unsigned char x_0, unsigned char x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint8_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_uint8_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint8_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* l_uint8_has__decidable__le(unsigned char x_0, unsigned char x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint8_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_uint8_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint8_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint16__sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(65536u);
return x_0;
}
}
obj* l_uint16_of__nat___boxed(obj* x_0) {
_start:
{
unsigned short x_1; obj* x_2; 
x_1 = lean::uint16_of_nat(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_uint16_to__nat___boxed(obj* x_0) {
_start:
{
unsigned short x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint16_to_nat(x_1);
return x_2;
}
}
obj* l_uint16_add___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; unsigned short x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_add(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; unsigned short x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_sub(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; unsigned short x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_mul(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_div___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; unsigned short x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_div(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; unsigned short x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_mod(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::uint16_modn(x_2, x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_uint16_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_uint16_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned short _init_l_uint16_has__zero() {
_start:
{
obj* x_0; unsigned short x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint16_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint16_has__zero___boxed() {
_start:
{
unsigned short x_0; obj* x_1; 
x_0 = l_uint16_has__zero;
x_1 = lean::box(x_0);
return x_1;
}
}
unsigned short _init_l_uint16_has__one() {
_start:
{
obj* x_0; unsigned short x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint16_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint16_has__one___boxed() {
_start:
{
unsigned short x_0; obj* x_1; 
x_0 = l_uint16_has__one;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_uint16_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint16_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init_l_uint16_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
unsigned short _init_l_uint16_inhabited() {
_start:
{
obj* x_0; unsigned short x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint16_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint16_inhabited___boxed() {
_start:
{
unsigned short x_0; obj* x_1; 
x_0 = l_uint16_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_uint16_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_uint16_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_dec_lt(x_2, x_3);
return x_4;
}
}
obj* l_uint16_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = lean::uint16_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint16_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint16_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_uint16_has__decidable__lt(unsigned short x_0, unsigned short x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint16_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_uint16_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint16_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* l_uint16_has__decidable__le(unsigned short x_0, unsigned short x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint16_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_uint16_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint16_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint32__sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967296"));
return x_0;
}
}
obj* l_uint32_of__nat___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
obj* l_uint32_to__nat___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l_uint32_add___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; unsigned x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_add(x_2, x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; unsigned x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_sub(x_2, x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; unsigned x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_mul(x_2, x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_div___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; unsigned x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_div(x_2, x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; unsigned x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_mod(x_2, x_3);
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::uint32_modn(x_2, x_1);
x_4 = lean::box_uint32(x_3);
return x_4;
}
}
obj* _init_l_uint32_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_uint32_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned _init_l_uint32_has__zero() {
_start:
{
obj* x_0; unsigned x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint32_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint32_has__zero___boxed() {
_start:
{
unsigned x_0; obj* x_1; 
x_0 = l_uint32_has__zero;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
unsigned _init_l_uint32_has__one() {
_start:
{
obj* x_0; unsigned x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint32_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint32_has__one___boxed() {
_start:
{
unsigned x_0; obj* x_1; 
x_0 = l_uint32_has__one;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_uint32_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint32_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init_l_uint32_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
unsigned _init_l_uint32_inhabited() {
_start:
{
obj* x_0; unsigned x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint32_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint32_inhabited___boxed() {
_start:
{
unsigned x_0; obj* x_1; 
x_0 = l_uint32_inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_uint32_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_uint32_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_dec_lt(x_2, x_3);
return x_4;
}
}
obj* l_uint32_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::uint32_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint32_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint32_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_uint32_has__decidable__lt(unsigned x_0, unsigned x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint32_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_uint32_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_uint32_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* l_uint32_has__decidable__le(unsigned x_0, unsigned x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint32_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_uint32_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_uint32_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint64__sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551616"));
return x_0;
}
}
obj* l_uint64_of__nat___boxed(obj* x_0) {
_start:
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::uint64_of_nat(x_0);
x_2 = lean::box_uint64(x_1);
return x_2;
}
}
obj* l_uint64_to__nat___boxed(obj* x_0) {
_start:
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = lean::uint64_to_nat(x_1);
return x_2;
}
}
obj* l_uint64_add___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; unsigned long long x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_add(x_2, x_3);
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; unsigned long long x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_sub(x_2, x_3);
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; unsigned long long x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_mul(x_2, x_3);
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_div___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; unsigned long long x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_div(x_2, x_3);
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; unsigned long long x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_mod(x_2, x_3);
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::uint64_modn(x_2, x_1);
x_4 = lean::box_uint64(x_3);
return x_4;
}
}
obj* _init_l_uint64_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_uint64_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
unsigned long long _init_l_uint64_has__zero() {
_start:
{
obj* x_0; unsigned long long x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint64_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint64_has__zero___boxed() {
_start:
{
unsigned long long x_0; obj* x_1; 
x_0 = l_uint64_has__zero;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
unsigned long long _init_l_uint64_has__one() {
_start:
{
obj* x_0; unsigned long long x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::uint64_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint64_has__one___boxed() {
_start:
{
unsigned long long x_0; obj* x_1; 
x_0 = l_uint64_has__one;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
obj* _init_l_uint64_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_uint64_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init_l_uint64_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
unsigned long long _init_l_uint64_inhabited() {
_start:
{
obj* x_0; unsigned long long x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::uint64_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_uint64_inhabited___boxed() {
_start:
{
unsigned long long x_0; obj* x_1; 
x_0 = l_uint64_inhabited;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
obj* l_uint64_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_uint64_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_dec_lt(x_2, x_3);
return x_4;
}
}
obj* l_uint64_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = lean::uint64_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init_l_uint64_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_uint64_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_uint64_has__decidable__lt(unsigned long long x_0, unsigned long long x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint64_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_uint64_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_uint64_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* l_uint64_has__decidable__le(unsigned long long x_0, unsigned long long x_1) {
_start:
{
obj* x_2; 
x_2 = lean::uint64_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_uint64_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_uint64_has__decidable__le(x_2, x_3);
return x_4;
}
}
void initialize_init_data_fin_basic();
static bool _G_initialized = false;
void initialize_init_data_uint() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_fin_basic();
 l_uint8__sz = _init_l_uint8__sz();
 l_uint8_lt = _init_l_uint8_lt();
 l_uint8_le = _init_l_uint8_le();
 l_uint8_has__zero = _init_l_uint8_has__zero();
 l_uint8_has__zero___boxed = _init_l_uint8_has__zero___boxed();
 l_uint8_has__one = _init_l_uint8_has__one();
 l_uint8_has__one___boxed = _init_l_uint8_has__one___boxed();
 l_uint8_has__add = _init_l_uint8_has__add();
 l_uint8_has__sub = _init_l_uint8_has__sub();
 l_uint8_has__mul = _init_l_uint8_has__mul();
 l_uint8_has__mod = _init_l_uint8_has__mod();
 l_uint8_has__modn = _init_l_uint8_has__modn();
 l_uint8_has__div = _init_l_uint8_has__div();
 l_uint8_has__lt = _init_l_uint8_has__lt();
 l_uint8_has__le = _init_l_uint8_has__le();
 l_uint8_inhabited = _init_l_uint8_inhabited();
 l_uint8_inhabited___boxed = _init_l_uint8_inhabited___boxed();
 l_uint8_decidable__eq = _init_l_uint8_decidable__eq();
 l_uint16__sz = _init_l_uint16__sz();
 l_uint16_lt = _init_l_uint16_lt();
 l_uint16_le = _init_l_uint16_le();
 l_uint16_has__zero = _init_l_uint16_has__zero();
 l_uint16_has__zero___boxed = _init_l_uint16_has__zero___boxed();
 l_uint16_has__one = _init_l_uint16_has__one();
 l_uint16_has__one___boxed = _init_l_uint16_has__one___boxed();
 l_uint16_has__add = _init_l_uint16_has__add();
 l_uint16_has__sub = _init_l_uint16_has__sub();
 l_uint16_has__mul = _init_l_uint16_has__mul();
 l_uint16_has__mod = _init_l_uint16_has__mod();
 l_uint16_has__modn = _init_l_uint16_has__modn();
 l_uint16_has__div = _init_l_uint16_has__div();
 l_uint16_has__lt = _init_l_uint16_has__lt();
 l_uint16_has__le = _init_l_uint16_has__le();
 l_uint16_inhabited = _init_l_uint16_inhabited();
 l_uint16_inhabited___boxed = _init_l_uint16_inhabited___boxed();
 l_uint16_decidable__eq = _init_l_uint16_decidable__eq();
 l_uint32__sz = _init_l_uint32__sz();
 l_uint32_lt = _init_l_uint32_lt();
 l_uint32_le = _init_l_uint32_le();
 l_uint32_has__zero = _init_l_uint32_has__zero();
 l_uint32_has__zero___boxed = _init_l_uint32_has__zero___boxed();
 l_uint32_has__one = _init_l_uint32_has__one();
 l_uint32_has__one___boxed = _init_l_uint32_has__one___boxed();
 l_uint32_has__add = _init_l_uint32_has__add();
 l_uint32_has__sub = _init_l_uint32_has__sub();
 l_uint32_has__mul = _init_l_uint32_has__mul();
 l_uint32_has__mod = _init_l_uint32_has__mod();
 l_uint32_has__modn = _init_l_uint32_has__modn();
 l_uint32_has__div = _init_l_uint32_has__div();
 l_uint32_has__lt = _init_l_uint32_has__lt();
 l_uint32_has__le = _init_l_uint32_has__le();
 l_uint32_inhabited = _init_l_uint32_inhabited();
 l_uint32_inhabited___boxed = _init_l_uint32_inhabited___boxed();
 l_uint32_decidable__eq = _init_l_uint32_decidable__eq();
 l_uint64__sz = _init_l_uint64__sz();
 l_uint64_lt = _init_l_uint64_lt();
 l_uint64_le = _init_l_uint64_le();
 l_uint64_has__zero = _init_l_uint64_has__zero();
 l_uint64_has__zero___boxed = _init_l_uint64_has__zero___boxed();
 l_uint64_has__one = _init_l_uint64_has__one();
 l_uint64_has__one___boxed = _init_l_uint64_has__one___boxed();
 l_uint64_has__add = _init_l_uint64_has__add();
 l_uint64_has__sub = _init_l_uint64_has__sub();
 l_uint64_has__mul = _init_l_uint64_has__mul();
 l_uint64_has__mod = _init_l_uint64_has__mod();
 l_uint64_has__modn = _init_l_uint64_has__modn();
 l_uint64_has__div = _init_l_uint64_has__div();
 l_uint64_has__lt = _init_l_uint64_has__lt();
 l_uint64_has__le = _init_l_uint64_has__le();
 l_uint64_inhabited = _init_l_uint64_inhabited();
 l_uint64_inhabited___boxed = _init_l_uint64_inhabited___boxed();
 l_uint64_decidable__eq = _init_l_uint64_decidable__eq();
}
