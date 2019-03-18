// Lean compiler output
// Module: init.data.uint
// Imports: init.data.fin.basic init.platform
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
obj* l_uint32_mul___boxed(obj*, obj*);
obj* l_uint8_div___boxed(obj*, obj*);
obj* l_usize_has__add;
namespace lean {
uint64 uint64_modn(uint64, obj*);
}
obj* l_uint8_has__le;
obj* l_uint16_inhabited___boxed;
obj* l_uint32_has__decidable__le___boxed(obj*, obj*);
uint8 l_uint32_has__decidable__lt(uint32, uint32);
uint8 l_uint8_has__decidable__lt(uint8, uint8);
obj* l_uint64_has__sub;
obj* l_uint8_inhabited___boxed;
obj* l_uint8_mod___boxed(obj*, obj*);
obj* l_usize_has__modn;
obj* l_uint16_land___boxed(obj*, obj*);
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_uint16_has__decidable__le___boxed(obj*, obj*);
obj* l_uint16_sub___boxed(obj*, obj*);
obj* l_uint16_has__sub;
obj* l_uint32_has__le;
obj* l_usize_mod___boxed(obj*, obj*);
uint8 l_uint16_has__decidable__le(uint16, uint16);
obj* l_uint64_add___boxed(obj*, obj*);
obj* l_uint16_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint8_add___boxed(obj*, obj*);
obj* l_uint16_dec__lt___boxed(obj*, obj*);
obj* l_usize_has__le;
obj* l_usize_dec__lt___boxed(obj*, obj*);
obj* l_uint64_inhabited___boxed;
obj* l_uint16_has__add;
uint8 l_uint32_has__decidable__le(uint32, uint32);
obj* l_uint16_lor___boxed(obj*, obj*);
obj* l_uint8_land___boxed(obj*, obj*);
uint32 l_uint32_inhabited;
obj* l_uint32_decidable__eq;
obj* l_uint32_has__mul;
obj* l_uint64_div___boxed(obj*, obj*);
extern obj* l_system_platform_nbits;
obj* l_uint64_dec__eq___boxed(obj*, obj*);
obj* l_usize_has__mod;
uint8 l_uint64_has__decidable__lt(uint64, uint64);
obj* l_uint32_has__sub;
uint8 l_uint8_inhabited;
obj* l_uint16_add___boxed(obj*, obj*);
obj* l_uint64_lor___boxed(obj*, obj*);
uint8 l_usize_has__decidable__le(usize, usize);
obj* l_usize_of__nat___boxed(obj*);
obj* l_uint16_modn___boxed(obj*, obj*);
obj* l_uint32_mod___boxed(obj*, obj*);
obj* l_uint32_has__lt;
obj* l_usize_has__div;
obj* l_uint32_has__zero___boxed;
obj* l_usize_dec__eq___boxed(obj*, obj*);
obj* l_uint16_has__le;
obj* l_uint32_sub___boxed(obj*, obj*);
obj* l_uint32_has__div;
obj* l_uint32_has__modn;
obj* l_uint64_has__decidable__le___boxed(obj*, obj*);
obj* l_uint8__sz;
namespace lean {
uint32 uint32_modn(uint32, obj*);
}
obj* l_usize_dec__le___boxed(obj*, obj*);
obj* l_uint64_has__mul;
namespace lean {
uint8 uint8_modn(uint8, obj*);
}
obj* l_uint8_has__decidable__le___boxed(obj*, obj*);
uint8 l_uint16_has__decidable__lt(uint16, uint16);
uint64 l_uint64_inhabited;
uint64 l_uint64_has__zero;
obj* l_usize_of__uint64___boxed(obj*);
obj* l_uint8_has__mod;
obj* l_uint16_div___boxed(obj*, obj*);
uint8 l_uint8_has__one;
obj* l_uint64_of__nat___boxed(obj*);
obj* l_usize_has__zero___boxed;
namespace lean {
uint16 uint16_of_nat(obj*);
}
obj* l_uint16_has__zero___boxed;
obj* l_uint8_has__zero___boxed;
obj* l_uint8_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint8_sub___boxed(obj*, obj*);
obj* l_uint32__sz;
obj* l_uint8_has__add;
obj* l_uint8_has__mul;
obj* l_uint8_has__modn;
obj* l_uint8_dec__le___boxed(obj*, obj*);
obj* l_uint32_has__mod;
obj* l_uint8_to__nat___boxed(obj*);
namespace lean {
uint16 uint16_modn(uint16, obj*);
}
obj* l_uint64_mul___boxed(obj*, obj*);
obj* l_usize_has__one___boxed;
obj* l_usize_div___boxed(obj*, obj*);
obj* l_usize_decidable__eq;
obj* l_uint16_to__nat___boxed(obj*);
obj* l_uint16_has__lt;
obj* l_uint8_has__sub;
uint32 l_uint32_has__zero;
obj* l_uint32_of__nat___boxed(obj*);
obj* l_usize_sub___boxed(obj*, obj*);
obj* l_uint8_mul___boxed(obj*, obj*);
obj* l_uint32_lor___boxed(obj*, obj*);
obj* l_uint16_has__div;
obj* l_usize_of__uint32___boxed(obj*);
obj* l_uint64_has__mod;
uint16 l_uint16_inhabited;
usize l_usize_inhabited;
obj* l_uint16_has__modn;
obj* l_usize_add___boxed(obj*, obj*);
obj* l_uint64__sz;
obj* l_usize_has__sub;
obj* l_usize_lor___boxed(obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
usize l_usize_has__zero;
obj* l_uint8_of__nat___boxed(obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_uint8_has__div;
uint64 l_uint64_has__one;
obj* l_uint16_decidable__eq;
obj* l_uint64_dec__lt___boxed(obj*, obj*);
obj* l_uint64_has__lt;
obj* l_uint64_has__div;
obj* l_uint16_mul___boxed(obj*, obj*);
obj* l_uint16_mod___boxed(obj*, obj*);
usize l_usize_has__one;
obj* l_uint32_dec__eq___boxed(obj*, obj*);
obj* l_uint64_has__one___boxed;
namespace lean {
uint64 uint64_of_nat(obj*);
}
uint8 l_uint8_has__zero;
obj* l_uint16_of__nat___boxed(obj*);
obj* l_uint32_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint64_land___boxed(obj*, obj*);
obj* l_uint32_modn___boxed(obj*, obj*);
namespace lean {
obj* uint8_to_nat(uint8);
}
obj* l_usize_has__decidable__lt___boxed(obj*, obj*);
obj* l_uint32_add___boxed(obj*, obj*);
obj* l_usize_has__lt;
obj* l_nat_pow___main(obj*, obj*);
obj* l_uint64_has__le;
obj* l_uint32_div___boxed(obj*, obj*);
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_usize_mul___boxed(obj*, obj*);
obj* l_uint16_has__one___boxed;
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_uint32_has__one___boxed;
obj* l_uint64_has__decidable__lt___boxed(obj*, obj*);
obj* l_usize__sz;
obj* l_uint64_mod___boxed(obj*, obj*);
obj* l_uint32_dec__lt___boxed(obj*, obj*);
obj* l_uint16_dec__eq___boxed(obj*, obj*);
obj* l_uint8_dec__eq___boxed(obj*, obj*);
obj* l_uint8_lor___boxed(obj*, obj*);
obj* l_uint16_dec__le___boxed(obj*, obj*);
obj* l_usize_has__decidable__le___boxed(obj*, obj*);
obj* l_uint8_decidable__eq;
obj* l_uint64_decidable__eq;
obj* l_uint32_land___boxed(obj*, obj*);
uint16 l_uint16_has__one;
obj* l_uint8_has__lt;
obj* l_uint8_dec__lt___boxed(obj*, obj*);
obj* l_uint64_to__nat___boxed(obj*);
obj* l_uint8_has__one___boxed;
uint8 l_usize_has__decidable__lt(usize, usize);
obj* l_uint16_has__mod;
obj* l_uint64_modn___boxed(obj*, obj*);
obj* l_uint8_modn___boxed(obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_uint32_inhabited___boxed;
obj* l_uint32_to__nat___boxed(obj*);
obj* l_uint16__sz;
obj* l_usize_to__nat___boxed(obj*);
obj* l_uint16_has__mul;
obj* l_usize_inhabited___boxed;
obj* l_uint64_has__modn;
obj* l_uint64_has__add;
obj* l_uint64_has__zero___boxed;
uint16 l_uint16_has__zero;
uint8 l_uint8_has__decidable__le(uint8, uint8);
obj* l_uint32_dec__le___boxed(obj*, obj*);
obj* l_uint64_dec__le___boxed(obj*, obj*);
uint32 l_uint32_has__one;
obj* l_uint64_sub___boxed(obj*, obj*);
obj* l_usize_land___boxed(obj*, obj*);
obj* l_uint32_has__add;
uint8 l_uint64_has__decidable__le(uint64, uint64);
namespace lean {
obj* usize_to_nat(usize);
}
namespace lean {
uint8 uint8_of_nat(obj*);
}
obj* l_usize_has__mul;
obj* l_usize_modn___boxed(obj*, obj*);
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
uint8 x_1; obj* x_2; 
x_1 = lean::uint8_of_nat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_uint8_to__nat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint8_to_nat(x_1);
return x_2;
}
}
obj* l_uint8_add___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 + x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 - x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 * x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_div___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_3 == 0 ? 0 : x_2 / x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_3 == 0 ? 0 : x_2 % x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::uint8_modn(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_uint8_land___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 & x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 | x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 _init_l_uint8_has__zero() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint8_has__zero___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_uint8_has__zero;
x_1 = lean::box(x_0);
return x_1;
}
}
uint8 _init_l_uint8_has__one() {
_start:
{
uint8 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_uint8_has__one___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
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
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_uint8_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 _init_l_uint8_inhabited() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint8_inhabited___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_uint8_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_uint8_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 == x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 < x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint8_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 <= x_3;
x_5 = lean::box(x_4);
return x_5;
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
uint8 l_uint8_has__decidable__lt(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_uint8_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint8_has__decidable__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_uint8_has__decidable__le(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_uint8_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint8_has__decidable__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
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
uint16 x_1; obj* x_2; 
x_1 = lean::uint16_of_nat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_uint16_to__nat___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint16_to_nat(x_1);
return x_2;
}
}
obj* l_uint16_add___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 + x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 - x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 * x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_div___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_3 == 0 ? 0 : x_2 / x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_3 == 0 ? 0 : x_2 % x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::uint16_modn(x_2, x_1);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_uint16_land___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 & x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint16 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 | x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
uint16 _init_l_uint16_has__zero() {
_start:
{
uint16 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint16_has__zero___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
x_0 = l_uint16_has__zero;
x_1 = lean::box(x_0);
return x_1;
}
}
uint16 _init_l_uint16_has__one() {
_start:
{
uint16 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_uint16_has__one___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
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
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_uint16_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint16 _init_l_uint16_inhabited() {
_start:
{
uint16 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint16_inhabited___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
x_0 = l_uint16_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_uint16_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 == x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 < x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint16_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = x_2 <= x_3;
x_5 = lean::box(x_4);
return x_5;
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
uint8 l_uint16_has__decidable__lt(uint16 x_0, uint16 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_uint16_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint16_has__decidable__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_uint16_has__decidable__le(uint16 x_0, uint16 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_uint16_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_uint16_has__decidable__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
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
uint32 x_1; obj* x_2; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_uint32_to__nat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l_uint32_add___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 + x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 - x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 * x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_div___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_3 == 0 ? 0 : x_2 / x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_3 == 0 ? 0 : x_2 % x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::uint32_modn(x_2, x_1);
x_4 = lean::box_uint32(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_uint32_land___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 & x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
obj* l_uint32_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint32 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 | x_3;
x_5 = lean::box_uint32(x_4);
return x_5;
}
}
uint32 _init_l_uint32_has__zero() {
_start:
{
uint32 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint32_has__zero___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_uint32_has__zero;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint32 _init_l_uint32_has__one() {
_start:
{
uint32 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_uint32_has__one___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
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
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_uint32_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint32 _init_l_uint32_inhabited() {
_start:
{
uint32 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint32_inhabited___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_uint32_inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_uint32_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 == x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint32_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 < x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint32_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = x_2 <= x_3;
x_5 = lean::box(x_4);
return x_5;
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
uint8 l_uint32_has__decidable__lt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_uint32_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_uint32_has__decidable__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_uint32_has__decidable__le(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_uint32_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_uint32_has__decidable__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
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
uint64 x_1; obj* x_2; 
x_1 = lean::uint64_of_nat(x_0);
x_2 = lean::box_uint64(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_uint64_to__nat___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = lean::uint64_to_nat(x_1);
return x_2;
}
}
obj* l_uint64_add___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 + x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 - x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 * x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_div___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_3 == 0 ? 0 : x_2 / x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_3 == 0 ? 0 : x_2 % x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::uint64_modn(x_2, x_1);
x_4 = lean::box_uint64(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_uint64_land___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 & x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
obj* l_uint64_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint64 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 | x_3;
x_5 = lean::box_uint64(x_4);
return x_5;
}
}
uint64 _init_l_uint64_has__zero() {
_start:
{
uint64 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint64_has__zero___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
x_0 = l_uint64_has__zero;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
uint64 _init_l_uint64_has__one() {
_start:
{
uint64 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_uint64_has__one___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
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
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_uint64_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint64 _init_l_uint64_inhabited() {
_start:
{
uint64 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_uint64_inhabited___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
x_0 = l_uint64_inhabited;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
obj* l_uint64_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 == x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint64_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 < x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_uint64_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = x_2 <= x_3;
x_5 = lean::box(x_4);
return x_5;
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
uint8 l_uint64_has__decidable__lt(uint64 x_0, uint64 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_uint64_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_uint64_has__decidable__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_uint64_has__decidable__le(uint64 x_0, uint64 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_uint64_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_uint64_has__decidable__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_usize__sz() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(2u);
x_1 = l_system_platform_nbits;
x_2 = l_nat_pow___main(x_0, x_1);
return x_2;
}
}
obj* l_usize_of__nat___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_usize_to__nat___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = lean::usize_to_nat(x_1);
return x_2;
}
}
obj* l_usize_add___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 + x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 - x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 * x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_div___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_3 == 0 ? 0 : x_2 / x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_3 == 0 ? 0 : x_2 % x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::usize_modn(x_2, x_1);
x_4 = lean::box_size_t(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_usize_land___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 & x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; usize x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 | x_3;
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_of__uint32___boxed(obj* x_0) {
_start:
{
uint32 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = x_1;
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* l_usize_of__uint64___boxed(obj* x_0) {
_start:
{
uint64 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint64(x_0);
x_2 = ((lean::usize)x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
usize _init_l_usize_has__zero() {
_start:
{
usize x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_usize_has__zero___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_usize_has__zero;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
usize _init_l_usize_has__one() {
_start:
{
usize x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_usize_has__one___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_usize_has__one;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _init_l_usize_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_usize_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
usize _init_l_usize_inhabited() {
_start:
{
usize x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_usize_inhabited___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_usize_inhabited;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* l_usize_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 == x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_usize_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 < x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_usize_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = x_2 <= x_3;
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_usize_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_dec__eq___boxed), 2, 0);
return x_0;
}
}
uint8 l_usize_has__decidable__lt(usize x_0, usize x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_usize_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_usize_has__decidable__lt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_usize_has__decidable__le(usize x_0, usize x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_usize_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_usize_has__decidable__le(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* initialize_init_data_fin_basic(obj*);
obj* initialize_init_platform(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_uint(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_platform(w);
 l_uint8__sz = _init_l_uint8__sz();
lean::mark_persistent(l_uint8__sz);
 l_uint8_has__zero = _init_l_uint8_has__zero();
 l_uint8_has__zero___boxed = _init_l_uint8_has__zero___boxed();
lean::mark_persistent(l_uint8_has__zero___boxed);
 l_uint8_has__one = _init_l_uint8_has__one();
 l_uint8_has__one___boxed = _init_l_uint8_has__one___boxed();
lean::mark_persistent(l_uint8_has__one___boxed);
 l_uint8_has__add = _init_l_uint8_has__add();
lean::mark_persistent(l_uint8_has__add);
 l_uint8_has__sub = _init_l_uint8_has__sub();
lean::mark_persistent(l_uint8_has__sub);
 l_uint8_has__mul = _init_l_uint8_has__mul();
lean::mark_persistent(l_uint8_has__mul);
 l_uint8_has__mod = _init_l_uint8_has__mod();
lean::mark_persistent(l_uint8_has__mod);
 l_uint8_has__modn = _init_l_uint8_has__modn();
lean::mark_persistent(l_uint8_has__modn);
 l_uint8_has__div = _init_l_uint8_has__div();
lean::mark_persistent(l_uint8_has__div);
 l_uint8_has__lt = _init_l_uint8_has__lt();
lean::mark_persistent(l_uint8_has__lt);
 l_uint8_has__le = _init_l_uint8_has__le();
lean::mark_persistent(l_uint8_has__le);
 l_uint8_inhabited = _init_l_uint8_inhabited();
 l_uint8_inhabited___boxed = _init_l_uint8_inhabited___boxed();
lean::mark_persistent(l_uint8_inhabited___boxed);
 l_uint8_decidable__eq = _init_l_uint8_decidable__eq();
lean::mark_persistent(l_uint8_decidable__eq);
 l_uint16__sz = _init_l_uint16__sz();
lean::mark_persistent(l_uint16__sz);
 l_uint16_has__zero = _init_l_uint16_has__zero();
 l_uint16_has__zero___boxed = _init_l_uint16_has__zero___boxed();
lean::mark_persistent(l_uint16_has__zero___boxed);
 l_uint16_has__one = _init_l_uint16_has__one();
 l_uint16_has__one___boxed = _init_l_uint16_has__one___boxed();
lean::mark_persistent(l_uint16_has__one___boxed);
 l_uint16_has__add = _init_l_uint16_has__add();
lean::mark_persistent(l_uint16_has__add);
 l_uint16_has__sub = _init_l_uint16_has__sub();
lean::mark_persistent(l_uint16_has__sub);
 l_uint16_has__mul = _init_l_uint16_has__mul();
lean::mark_persistent(l_uint16_has__mul);
 l_uint16_has__mod = _init_l_uint16_has__mod();
lean::mark_persistent(l_uint16_has__mod);
 l_uint16_has__modn = _init_l_uint16_has__modn();
lean::mark_persistent(l_uint16_has__modn);
 l_uint16_has__div = _init_l_uint16_has__div();
lean::mark_persistent(l_uint16_has__div);
 l_uint16_has__lt = _init_l_uint16_has__lt();
lean::mark_persistent(l_uint16_has__lt);
 l_uint16_has__le = _init_l_uint16_has__le();
lean::mark_persistent(l_uint16_has__le);
 l_uint16_inhabited = _init_l_uint16_inhabited();
 l_uint16_inhabited___boxed = _init_l_uint16_inhabited___boxed();
lean::mark_persistent(l_uint16_inhabited___boxed);
 l_uint16_decidable__eq = _init_l_uint16_decidable__eq();
lean::mark_persistent(l_uint16_decidable__eq);
 l_uint32__sz = _init_l_uint32__sz();
lean::mark_persistent(l_uint32__sz);
 l_uint32_has__zero = _init_l_uint32_has__zero();
 l_uint32_has__zero___boxed = _init_l_uint32_has__zero___boxed();
lean::mark_persistent(l_uint32_has__zero___boxed);
 l_uint32_has__one = _init_l_uint32_has__one();
 l_uint32_has__one___boxed = _init_l_uint32_has__one___boxed();
lean::mark_persistent(l_uint32_has__one___boxed);
 l_uint32_has__add = _init_l_uint32_has__add();
lean::mark_persistent(l_uint32_has__add);
 l_uint32_has__sub = _init_l_uint32_has__sub();
lean::mark_persistent(l_uint32_has__sub);
 l_uint32_has__mul = _init_l_uint32_has__mul();
lean::mark_persistent(l_uint32_has__mul);
 l_uint32_has__mod = _init_l_uint32_has__mod();
lean::mark_persistent(l_uint32_has__mod);
 l_uint32_has__modn = _init_l_uint32_has__modn();
lean::mark_persistent(l_uint32_has__modn);
 l_uint32_has__div = _init_l_uint32_has__div();
lean::mark_persistent(l_uint32_has__div);
 l_uint32_has__lt = _init_l_uint32_has__lt();
lean::mark_persistent(l_uint32_has__lt);
 l_uint32_has__le = _init_l_uint32_has__le();
lean::mark_persistent(l_uint32_has__le);
 l_uint32_inhabited = _init_l_uint32_inhabited();
 l_uint32_inhabited___boxed = _init_l_uint32_inhabited___boxed();
lean::mark_persistent(l_uint32_inhabited___boxed);
 l_uint32_decidable__eq = _init_l_uint32_decidable__eq();
lean::mark_persistent(l_uint32_decidable__eq);
 l_uint64__sz = _init_l_uint64__sz();
lean::mark_persistent(l_uint64__sz);
 l_uint64_has__zero = _init_l_uint64_has__zero();
 l_uint64_has__zero___boxed = _init_l_uint64_has__zero___boxed();
lean::mark_persistent(l_uint64_has__zero___boxed);
 l_uint64_has__one = _init_l_uint64_has__one();
 l_uint64_has__one___boxed = _init_l_uint64_has__one___boxed();
lean::mark_persistent(l_uint64_has__one___boxed);
 l_uint64_has__add = _init_l_uint64_has__add();
lean::mark_persistent(l_uint64_has__add);
 l_uint64_has__sub = _init_l_uint64_has__sub();
lean::mark_persistent(l_uint64_has__sub);
 l_uint64_has__mul = _init_l_uint64_has__mul();
lean::mark_persistent(l_uint64_has__mul);
 l_uint64_has__mod = _init_l_uint64_has__mod();
lean::mark_persistent(l_uint64_has__mod);
 l_uint64_has__modn = _init_l_uint64_has__modn();
lean::mark_persistent(l_uint64_has__modn);
 l_uint64_has__div = _init_l_uint64_has__div();
lean::mark_persistent(l_uint64_has__div);
 l_uint64_has__lt = _init_l_uint64_has__lt();
lean::mark_persistent(l_uint64_has__lt);
 l_uint64_has__le = _init_l_uint64_has__le();
lean::mark_persistent(l_uint64_has__le);
 l_uint64_inhabited = _init_l_uint64_inhabited();
 l_uint64_inhabited___boxed = _init_l_uint64_inhabited___boxed();
lean::mark_persistent(l_uint64_inhabited___boxed);
 l_uint64_decidable__eq = _init_l_uint64_decidable__eq();
lean::mark_persistent(l_uint64_decidable__eq);
 l_usize__sz = _init_l_usize__sz();
lean::mark_persistent(l_usize__sz);
 l_usize_has__zero = _init_l_usize_has__zero();
 l_usize_has__zero___boxed = _init_l_usize_has__zero___boxed();
lean::mark_persistent(l_usize_has__zero___boxed);
 l_usize_has__one = _init_l_usize_has__one();
 l_usize_has__one___boxed = _init_l_usize_has__one___boxed();
lean::mark_persistent(l_usize_has__one___boxed);
 l_usize_has__add = _init_l_usize_has__add();
lean::mark_persistent(l_usize_has__add);
 l_usize_has__sub = _init_l_usize_has__sub();
lean::mark_persistent(l_usize_has__sub);
 l_usize_has__mul = _init_l_usize_has__mul();
lean::mark_persistent(l_usize_has__mul);
 l_usize_has__mod = _init_l_usize_has__mod();
lean::mark_persistent(l_usize_has__mod);
 l_usize_has__modn = _init_l_usize_has__modn();
lean::mark_persistent(l_usize_has__modn);
 l_usize_has__div = _init_l_usize_has__div();
lean::mark_persistent(l_usize_has__div);
 l_usize_has__lt = _init_l_usize_has__lt();
lean::mark_persistent(l_usize_has__lt);
 l_usize_has__le = _init_l_usize_has__le();
lean::mark_persistent(l_usize_has__le);
 l_usize_inhabited = _init_l_usize_inhabited();
 l_usize_inhabited___boxed = _init_l_usize_inhabited___boxed();
lean::mark_persistent(l_usize_inhabited___boxed);
 l_usize_decidable__eq = _init_l_usize_decidable__eq();
lean::mark_persistent(l_usize_decidable__eq);
return w;
}
