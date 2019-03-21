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
obj* l_UInt8_hasDecidableLt___boxed(obj*, obj*);
uint8 l_UInt8_Inhabited;
namespace lean {
obj* uint8_to_nat(uint8);
}
obj* l_UInt32_mul___boxed(obj*, obj*);
namespace lean {
uint16 uint16_modn(uint16, obj*);
}
obj* l_UInt8_land___boxed(obj*, obj*);
obj* l_UInt64_HasMod;
obj* l_UInt32_HasDiv;
obj* l_UInt64_HasOne___boxed;
uint8 l_UInt16_hasDecidableLe(uint16, uint16);
uint16 l_UInt16_HasZero;
obj* l_UInt64_HasSub;
obj* l_UInt32_Inhabited___boxed;
obj* l_UInt64_Inhabited___boxed;
obj* l_UInt16_DecidableEq;
obj* l_UInt64_ofNat___boxed(obj*);
obj* l_UInt16_modn___boxed(obj*, obj*);
obj* l_UInt32_HasZero___boxed;
namespace lean {
uint8 uint8_modn(uint8, obj*);
}
obj* l_UInt8_HasOne___boxed;
obj* l_UInt32_hasDecidableLt___boxed(obj*, obj*);
obj* l_UInt32_HasOne___boxed;
obj* l_UInt8_decLe___boxed(obj*, obj*);
obj* l_UInt64_HasModn;
obj* l_UInt64_hasDecidableLe___boxed(obj*, obj*);
namespace lean {
uint8 uint8_of_nat(obj*);
}
obj* l_UInt64_div___boxed(obj*, obj*);
namespace lean {
uint16 uint16_of_nat(obj*);
}
obj* l_UInt32_HasAdd;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_UInt16_lor___boxed(obj*, obj*);
uint64 l_UInt64_HasZero;
obj* l_UInt8_HasSub;
obj* l_UInt8_decLt___boxed(obj*, obj*);
obj* l_UInt32_lor___boxed(obj*, obj*);
obj* l_USize_mul___boxed(obj*, obj*);
extern obj* l_System_platform_nbits;
obj* l_UInt16_HasLe;
obj* l_USize_HasZero___boxed;
obj* l_USize_decLe___boxed(obj*, obj*);
obj* l_USize_div___boxed(obj*, obj*);
obj* l_uint32Sz;
obj* l_UInt64_HasDiv;
obj* l_USize_HasDiv;
obj* l_uint64Sz;
usize l_USize_HasZero;
obj* l_UInt64_HasMul;
obj* l_UInt16_toNat___boxed(obj*);
obj* l_UInt32_decLt___boxed(obj*, obj*);
obj* l_UInt64_decLt___boxed(obj*, obj*);
obj* l_USize_hasDecidableLe___boxed(obj*, obj*);
obj* l_UInt32_div___boxed(obj*, obj*);
uint64 l_UInt64_Inhabited;
uint8 l_UInt8_hasDecidableLt(uint8, uint8);
obj* l_UInt16_land___boxed(obj*, obj*);
obj* l_USize_modn___boxed(obj*, obj*);
obj* l_UInt16_HasLt;
obj* l_UInt16_hasDecidableLe___boxed(obj*, obj*);
obj* l_UInt8_modn___boxed(obj*, obj*);
obj* l_USize_sub___boxed(obj*, obj*);
obj* l_USize_ofUInt64___boxed(obj*);
namespace lean {
uint64 uint64_of_nat(obj*);
}
obj* l_UInt64_HasLe;
obj* l_USize_HasMod;
obj* l_UInt8_HasZero___boxed;
obj* l_UInt16_decLe___boxed(obj*, obj*);
obj* l_USize_HasOne___boxed;
obj* l_UInt64_add___boxed(obj*, obj*);
usize l_USize_HasOne;
obj* l_UInt16_HasModn;
obj* l_UInt64_land___boxed(obj*, obj*);
obj* l_UInt32_decEq___boxed(obj*, obj*);
obj* l_USize_decLt___boxed(obj*, obj*);
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_UInt8_HasAdd;
uint8 l_UInt8_HasZero;
obj* l_UInt8_hasDecidableLe___boxed(obj*, obj*);
obj* l_UInt16_div___boxed(obj*, obj*);
obj* l_UInt32_modn___boxed(obj*, obj*);
obj* l_USize_add___boxed(obj*, obj*);
obj* l_UInt32_add___boxed(obj*, obj*);
uint8 l_UInt32_hasDecidableLe(uint32, uint32);
obj* l_USize_DecidableEq;
obj* l_UInt8_sub___boxed(obj*, obj*);
obj* l_UInt64_sub___boxed(obj*, obj*);
obj* l_UInt32_HasMul;
uint8 l_UInt64_hasDecidableLe(uint64, uint64);
obj* l_UInt32_HasMod;
obj* l_USize_HasMul;
obj* l_UInt16_add___boxed(obj*, obj*);
uint32 l_UInt32_HasZero;
uint8 l_UInt8_hasDecidableLe(uint8, uint8);
obj* l_UInt32_ofNat___boxed(obj*);
obj* l_UInt8_DecidableEq;
obj* l_UInt8_Inhabited___boxed;
obj* l_UInt8_ofNat___boxed(obj*);
obj* l_UInt16_mul___boxed(obj*, obj*);
obj* l_UInt16_HasZero___boxed;
obj* l_uint8Sz;
obj* l_UInt64_decLe___boxed(obj*, obj*);
obj* l_UInt32_HasLe;
obj* l_USize_HasLt;
obj* l_USize_land___boxed(obj*, obj*);
obj* l_UInt16_hasDecidableLt___boxed(obj*, obj*);
obj* l_UInt32_sub___boxed(obj*, obj*);
obj* l_UInt8_add___boxed(obj*, obj*);
obj* l_USize_HasSub;
obj* l_UInt16_Inhabited___boxed;
obj* l_UInt8_toNat___boxed(obj*);
obj* l_USize_hasDecidableLt___boxed(obj*, obj*);
obj* l_UInt64_HasZero___boxed;
uint8 l_UInt32_hasDecidableLt(uint32, uint32);
obj* l_UInt64_HasAdd;
obj* l_USize_ofUInt32___boxed(obj*);
obj* l_USize_lor___boxed(obj*, obj*);
uint64 l_UInt64_HasOne;
uint8 l_UInt16_hasDecidableLt(uint16, uint16);
uint8 l_UInt64_hasDecidableLt(uint64, uint64);
obj* l_UInt32_HasModn;
obj* l_UInt8_HasDiv;
obj* l_UInt64_toNat___boxed(obj*);
obj* l_Nat_pow___main(obj*, obj*);
obj* l_UInt32_HasLt;
obj* l_UInt16_HasMod;
obj* l_UInt32_land___boxed(obj*, obj*);
obj* l_UInt16_HasMul;
obj* l_USize_decEq___boxed(obj*, obj*);
obj* l_UInt8_decEq___boxed(obj*, obj*);
obj* l_UInt64_hasDecidableLt___boxed(obj*, obj*);
obj* l_UInt16_HasAdd;
obj* l_USize_mod___boxed(obj*, obj*);
obj* l_UInt16_mod___boxed(obj*, obj*);
obj* l_UInt16_HasSub;
obj* l_USize_ofNat___boxed(obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_USize_HasAdd;
obj* l_USize_toNat___boxed(obj*);
obj* l_USize_HasLe;
obj* l_UInt32_DecidableEq;
obj* l_UInt8_mul___boxed(obj*, obj*);
obj* l_UInt32_decLe___boxed(obj*, obj*);
obj* l_UInt64_modn___boxed(obj*, obj*);
obj* l_UInt64_mul___boxed(obj*, obj*);
obj* l_USize_HasModn;
obj* l_UInt16_ofNat___boxed(obj*);
obj* l_UInt8_HasLt;
obj* l_UInt8_HasModn;
obj* l_uint16Sz;
obj* l_UInt32_hasDecidableLe___boxed(obj*, obj*);
obj* l_USize_Inhabited___boxed;
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_UInt32_HasSub;
uint16 l_UInt16_HasOne;
obj* l_UInt8_HasMod;
obj* l_usizeSz;
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_UInt64_mod___boxed(obj*, obj*);
obj* l_UInt8_HasLe;
obj* l_UInt64_HasLt;
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_UInt8_div___boxed(obj*, obj*);
obj* l_UInt32_toNat___boxed(obj*);
obj* l_UInt64_decEq___boxed(obj*, obj*);
uint32 l_UInt32_Inhabited;
obj* l_UInt8_lor___boxed(obj*, obj*);
obj* l_UInt8_mod___boxed(obj*, obj*);
obj* l_UInt8_HasMul;
obj* l_UInt16_HasOne___boxed;
uint8 l_USize_hasDecidableLt(usize, usize);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_UInt16_HasDiv;
usize l_USize_Inhabited;
obj* l_UInt16_decEq___boxed(obj*, obj*);
namespace lean {
uint64 uint64_modn(uint64, obj*);
}
obj* l_UInt16_decLt___boxed(obj*, obj*);
namespace lean {
uint32 uint32_modn(uint32, obj*);
}
uint16 l_UInt16_Inhabited;
obj* l_UInt64_DecidableEq;
obj* l_UInt64_lor___boxed(obj*, obj*);
obj* l_UInt16_sub___boxed(obj*, obj*);
uint8 l_USize_hasDecidableLe(usize, usize);
obj* l_UInt32_mod___boxed(obj*, obj*);
uint8 l_UInt8_HasOne;
uint32 l_UInt32_HasOne;
obj* _init_l_uint8Sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(256u);
return x_0;
}
}
obj* l_UInt8_ofNat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::uint8_of_nat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_UInt8_toNat___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint8_to_nat(x_1);
return x_2;
}
}
obj* l_UInt8_add___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_sub___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_mul___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_div___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_mod___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_modn___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_land___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_lor___boxed(obj* x_0, obj* x_1) {
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
uint8 _init_l_UInt8_HasZero() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt8_HasZero___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_UInt8_HasZero;
x_1 = lean::box(x_0);
return x_1;
}
}
uint8 _init_l_UInt8_HasOne() {
_start:
{
uint8 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_UInt8_HasOne___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_UInt8_HasOne;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_UInt8_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasModn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt8_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_UInt8_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 _init_l_UInt8_Inhabited() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt8_Inhabited___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_UInt8_Inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_UInt8_decEq___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_decLt___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt8_decLe___boxed(obj* x_0, obj* x_1) {
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
obj* _init_l_UInt8_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt8_decEq___boxed), 2, 0);
return x_0;
}
}
uint8 l_UInt8_hasDecidableLt(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_UInt8_hasDecidableLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_UInt8_hasDecidableLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_UInt8_hasDecidableLe(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_UInt8_hasDecidableLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_UInt8_hasDecidableLe(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_uint16Sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(65536u);
return x_0;
}
}
obj* l_UInt16_ofNat___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::uint16_of_nat(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_UInt16_toNat___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = lean::uint16_to_nat(x_1);
return x_2;
}
}
obj* l_UInt16_add___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_sub___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_mul___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_div___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_mod___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_modn___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_land___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_lor___boxed(obj* x_0, obj* x_1) {
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
uint16 _init_l_UInt16_HasZero() {
_start:
{
uint16 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt16_HasZero___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
x_0 = l_UInt16_HasZero;
x_1 = lean::box(x_0);
return x_1;
}
}
uint16 _init_l_UInt16_HasOne() {
_start:
{
uint16 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_UInt16_HasOne___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
x_0 = l_UInt16_HasOne;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* _init_l_UInt16_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasModn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt16_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_UInt16_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint16 _init_l_UInt16_Inhabited() {
_start:
{
uint16 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt16_Inhabited___boxed() {
_start:
{
uint16 x_0; obj* x_1; 
x_0 = l_UInt16_Inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
obj* l_UInt16_decEq___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_decLt___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt16_decLe___boxed(obj* x_0, obj* x_1) {
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
obj* _init_l_UInt16_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt16_decEq___boxed), 2, 0);
return x_0;
}
}
uint8 l_UInt16_hasDecidableLt(uint16 x_0, uint16 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_UInt16_hasDecidableLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_UInt16_hasDecidableLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_UInt16_hasDecidableLe(uint16 x_0, uint16 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_UInt16_hasDecidableLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint16 x_2; uint16 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_UInt16_hasDecidableLe(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_uint32Sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967296"));
return x_0;
}
}
obj* l_UInt32_ofNat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::uint32_of_nat(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_UInt32_toNat___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = lean::uint32_to_nat(x_1);
return x_2;
}
}
obj* l_UInt32_add___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_sub___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_mul___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_div___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_mod___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_modn___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_land___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_lor___boxed(obj* x_0, obj* x_1) {
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
uint32 _init_l_UInt32_HasZero() {
_start:
{
uint32 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt32_HasZero___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_UInt32_HasZero;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
uint32 _init_l_UInt32_HasOne() {
_start:
{
uint32 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_UInt32_HasOne___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_UInt32_HasOne;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* _init_l_UInt32_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasModn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt32_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_UInt32_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint32 _init_l_UInt32_Inhabited() {
_start:
{
uint32 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt32_Inhabited___boxed() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = l_UInt32_Inhabited;
x_1 = lean::box_uint32(x_0);
return x_1;
}
}
obj* l_UInt32_decEq___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_decLt___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt32_decLe___boxed(obj* x_0, obj* x_1) {
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
obj* _init_l_UInt32_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt32_decEq___boxed), 2, 0);
return x_0;
}
}
uint8 l_UInt32_hasDecidableLt(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_UInt32_hasDecidableLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_UInt32_hasDecidableLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_UInt32_hasDecidableLe(uint32 x_0, uint32 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_UInt32_hasDecidableLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; uint32 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = l_UInt32_hasDecidableLe(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_uint64Sz() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551616"));
return x_0;
}
}
obj* l_UInt64_ofNat___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::uint64_of_nat(x_0);
x_2 = lean::box_uint64(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_UInt64_toNat___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = lean::uint64_to_nat(x_1);
return x_2;
}
}
obj* l_UInt64_add___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_sub___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_mul___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_div___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_mod___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_modn___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_land___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_lor___boxed(obj* x_0, obj* x_1) {
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
uint64 _init_l_UInt64_HasZero() {
_start:
{
uint64 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt64_HasZero___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
x_0 = l_UInt64_HasZero;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
uint64 _init_l_UInt64_HasOne() {
_start:
{
uint64 x_0; 
x_0 = 1;
return x_0;
}
}
obj* _init_l_UInt64_HasOne___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
x_0 = l_UInt64_HasOne;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
obj* _init_l_UInt64_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasModn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_UInt64_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_UInt64_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint64 _init_l_UInt64_Inhabited() {
_start:
{
uint64 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_UInt64_Inhabited___boxed() {
_start:
{
uint64 x_0; obj* x_1; 
x_0 = l_UInt64_Inhabited;
x_1 = lean::box_uint64(x_0);
return x_1;
}
}
obj* l_UInt64_decEq___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_decLt___boxed(obj* x_0, obj* x_1) {
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
obj* l_UInt64_decLe___boxed(obj* x_0, obj* x_1) {
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
obj* _init_l_UInt64_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_UInt64_decEq___boxed), 2, 0);
return x_0;
}
}
uint8 l_UInt64_hasDecidableLt(uint64 x_0, uint64 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_UInt64_hasDecidableLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_UInt64_hasDecidableLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_UInt64_hasDecidableLe(uint64 x_0, uint64 x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_UInt64_hasDecidableLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint64 x_2; uint64 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = l_UInt64_hasDecidableLe(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_usizeSz() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(2u);
x_1 = l_System_platform_nbits;
x_2 = l_Nat_pow___main(x_0, x_1);
return x_2;
}
}
obj* l_USize_ofNat___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_USize_toNat___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = lean::usize_to_nat(x_1);
return x_2;
}
}
obj* l_USize_add___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_sub___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_mul___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_div___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_mod___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_modn___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_land___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_lor___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_ofUInt32___boxed(obj* x_0) {
_start:
{
uint32 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = x_1;
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* l_USize_ofUInt64___boxed(obj* x_0) {
_start:
{
uint64 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint64(x_0);
x_2 = ((lean::usize)x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
usize _init_l_USize_HasZero() {
_start:
{
obj* x_0; usize x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* _init_l_USize_HasZero___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_USize_HasZero;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
usize _init_l_USize_HasOne() {
_start:
{
obj* x_0; usize x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* _init_l_USize_HasOne___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_USize_HasOne;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _init_l_USize_HasAdd() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasMod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasModn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasDiv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_USize_HasLt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_USize_HasLe() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
usize _init_l_USize_Inhabited() {
_start:
{
obj* x_0; usize x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* _init_l_USize_Inhabited___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_USize_Inhabited;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* l_USize_decEq___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_decLt___boxed(obj* x_0, obj* x_1) {
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
obj* l_USize_decLe___boxed(obj* x_0, obj* x_1) {
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
obj* _init_l_USize_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_USize_decEq___boxed), 2, 0);
return x_0;
}
}
uint8 l_USize_hasDecidableLt(usize x_0, usize x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 < x_1;
return x_2;
}
}
obj* l_USize_hasDecidableLt___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_USize_hasDecidableLt(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_USize_hasDecidableLe(usize x_0, usize x_1) {
_start:
{
uint8 x_2; 
x_2 = x_0 <= x_1;
return x_2;
}
}
obj* l_USize_hasDecidableLe___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_USize_hasDecidableLe(x_2, x_3);
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
 l_uint8Sz = _init_l_uint8Sz();
lean::mark_persistent(l_uint8Sz);
 l_UInt8_HasZero = _init_l_UInt8_HasZero();
 l_UInt8_HasZero___boxed = _init_l_UInt8_HasZero___boxed();
lean::mark_persistent(l_UInt8_HasZero___boxed);
 l_UInt8_HasOne = _init_l_UInt8_HasOne();
 l_UInt8_HasOne___boxed = _init_l_UInt8_HasOne___boxed();
lean::mark_persistent(l_UInt8_HasOne___boxed);
 l_UInt8_HasAdd = _init_l_UInt8_HasAdd();
lean::mark_persistent(l_UInt8_HasAdd);
 l_UInt8_HasSub = _init_l_UInt8_HasSub();
lean::mark_persistent(l_UInt8_HasSub);
 l_UInt8_HasMul = _init_l_UInt8_HasMul();
lean::mark_persistent(l_UInt8_HasMul);
 l_UInt8_HasMod = _init_l_UInt8_HasMod();
lean::mark_persistent(l_UInt8_HasMod);
 l_UInt8_HasModn = _init_l_UInt8_HasModn();
lean::mark_persistent(l_UInt8_HasModn);
 l_UInt8_HasDiv = _init_l_UInt8_HasDiv();
lean::mark_persistent(l_UInt8_HasDiv);
 l_UInt8_HasLt = _init_l_UInt8_HasLt();
lean::mark_persistent(l_UInt8_HasLt);
 l_UInt8_HasLe = _init_l_UInt8_HasLe();
lean::mark_persistent(l_UInt8_HasLe);
 l_UInt8_Inhabited = _init_l_UInt8_Inhabited();
 l_UInt8_Inhabited___boxed = _init_l_UInt8_Inhabited___boxed();
lean::mark_persistent(l_UInt8_Inhabited___boxed);
 l_UInt8_DecidableEq = _init_l_UInt8_DecidableEq();
lean::mark_persistent(l_UInt8_DecidableEq);
 l_uint16Sz = _init_l_uint16Sz();
lean::mark_persistent(l_uint16Sz);
 l_UInt16_HasZero = _init_l_UInt16_HasZero();
 l_UInt16_HasZero___boxed = _init_l_UInt16_HasZero___boxed();
lean::mark_persistent(l_UInt16_HasZero___boxed);
 l_UInt16_HasOne = _init_l_UInt16_HasOne();
 l_UInt16_HasOne___boxed = _init_l_UInt16_HasOne___boxed();
lean::mark_persistent(l_UInt16_HasOne___boxed);
 l_UInt16_HasAdd = _init_l_UInt16_HasAdd();
lean::mark_persistent(l_UInt16_HasAdd);
 l_UInt16_HasSub = _init_l_UInt16_HasSub();
lean::mark_persistent(l_UInt16_HasSub);
 l_UInt16_HasMul = _init_l_UInt16_HasMul();
lean::mark_persistent(l_UInt16_HasMul);
 l_UInt16_HasMod = _init_l_UInt16_HasMod();
lean::mark_persistent(l_UInt16_HasMod);
 l_UInt16_HasModn = _init_l_UInt16_HasModn();
lean::mark_persistent(l_UInt16_HasModn);
 l_UInt16_HasDiv = _init_l_UInt16_HasDiv();
lean::mark_persistent(l_UInt16_HasDiv);
 l_UInt16_HasLt = _init_l_UInt16_HasLt();
lean::mark_persistent(l_UInt16_HasLt);
 l_UInt16_HasLe = _init_l_UInt16_HasLe();
lean::mark_persistent(l_UInt16_HasLe);
 l_UInt16_Inhabited = _init_l_UInt16_Inhabited();
 l_UInt16_Inhabited___boxed = _init_l_UInt16_Inhabited___boxed();
lean::mark_persistent(l_UInt16_Inhabited___boxed);
 l_UInt16_DecidableEq = _init_l_UInt16_DecidableEq();
lean::mark_persistent(l_UInt16_DecidableEq);
 l_uint32Sz = _init_l_uint32Sz();
lean::mark_persistent(l_uint32Sz);
 l_UInt32_HasZero = _init_l_UInt32_HasZero();
 l_UInt32_HasZero___boxed = _init_l_UInt32_HasZero___boxed();
lean::mark_persistent(l_UInt32_HasZero___boxed);
 l_UInt32_HasOne = _init_l_UInt32_HasOne();
 l_UInt32_HasOne___boxed = _init_l_UInt32_HasOne___boxed();
lean::mark_persistent(l_UInt32_HasOne___boxed);
 l_UInt32_HasAdd = _init_l_UInt32_HasAdd();
lean::mark_persistent(l_UInt32_HasAdd);
 l_UInt32_HasSub = _init_l_UInt32_HasSub();
lean::mark_persistent(l_UInt32_HasSub);
 l_UInt32_HasMul = _init_l_UInt32_HasMul();
lean::mark_persistent(l_UInt32_HasMul);
 l_UInt32_HasMod = _init_l_UInt32_HasMod();
lean::mark_persistent(l_UInt32_HasMod);
 l_UInt32_HasModn = _init_l_UInt32_HasModn();
lean::mark_persistent(l_UInt32_HasModn);
 l_UInt32_HasDiv = _init_l_UInt32_HasDiv();
lean::mark_persistent(l_UInt32_HasDiv);
 l_UInt32_HasLt = _init_l_UInt32_HasLt();
lean::mark_persistent(l_UInt32_HasLt);
 l_UInt32_HasLe = _init_l_UInt32_HasLe();
lean::mark_persistent(l_UInt32_HasLe);
 l_UInt32_Inhabited = _init_l_UInt32_Inhabited();
 l_UInt32_Inhabited___boxed = _init_l_UInt32_Inhabited___boxed();
lean::mark_persistent(l_UInt32_Inhabited___boxed);
 l_UInt32_DecidableEq = _init_l_UInt32_DecidableEq();
lean::mark_persistent(l_UInt32_DecidableEq);
 l_uint64Sz = _init_l_uint64Sz();
lean::mark_persistent(l_uint64Sz);
 l_UInt64_HasZero = _init_l_UInt64_HasZero();
 l_UInt64_HasZero___boxed = _init_l_UInt64_HasZero___boxed();
lean::mark_persistent(l_UInt64_HasZero___boxed);
 l_UInt64_HasOne = _init_l_UInt64_HasOne();
 l_UInt64_HasOne___boxed = _init_l_UInt64_HasOne___boxed();
lean::mark_persistent(l_UInt64_HasOne___boxed);
 l_UInt64_HasAdd = _init_l_UInt64_HasAdd();
lean::mark_persistent(l_UInt64_HasAdd);
 l_UInt64_HasSub = _init_l_UInt64_HasSub();
lean::mark_persistent(l_UInt64_HasSub);
 l_UInt64_HasMul = _init_l_UInt64_HasMul();
lean::mark_persistent(l_UInt64_HasMul);
 l_UInt64_HasMod = _init_l_UInt64_HasMod();
lean::mark_persistent(l_UInt64_HasMod);
 l_UInt64_HasModn = _init_l_UInt64_HasModn();
lean::mark_persistent(l_UInt64_HasModn);
 l_UInt64_HasDiv = _init_l_UInt64_HasDiv();
lean::mark_persistent(l_UInt64_HasDiv);
 l_UInt64_HasLt = _init_l_UInt64_HasLt();
lean::mark_persistent(l_UInt64_HasLt);
 l_UInt64_HasLe = _init_l_UInt64_HasLe();
lean::mark_persistent(l_UInt64_HasLe);
 l_UInt64_Inhabited = _init_l_UInt64_Inhabited();
 l_UInt64_Inhabited___boxed = _init_l_UInt64_Inhabited___boxed();
lean::mark_persistent(l_UInt64_Inhabited___boxed);
 l_UInt64_DecidableEq = _init_l_UInt64_DecidableEq();
lean::mark_persistent(l_UInt64_DecidableEq);
 l_usizeSz = _init_l_usizeSz();
lean::mark_persistent(l_usizeSz);
 l_USize_HasZero = _init_l_USize_HasZero();
 l_USize_HasZero___boxed = _init_l_USize_HasZero___boxed();
lean::mark_persistent(l_USize_HasZero___boxed);
 l_USize_HasOne = _init_l_USize_HasOne();
 l_USize_HasOne___boxed = _init_l_USize_HasOne___boxed();
lean::mark_persistent(l_USize_HasOne___boxed);
 l_USize_HasAdd = _init_l_USize_HasAdd();
lean::mark_persistent(l_USize_HasAdd);
 l_USize_HasSub = _init_l_USize_HasSub();
lean::mark_persistent(l_USize_HasSub);
 l_USize_HasMul = _init_l_USize_HasMul();
lean::mark_persistent(l_USize_HasMul);
 l_USize_HasMod = _init_l_USize_HasMod();
lean::mark_persistent(l_USize_HasMod);
 l_USize_HasModn = _init_l_USize_HasModn();
lean::mark_persistent(l_USize_HasModn);
 l_USize_HasDiv = _init_l_USize_HasDiv();
lean::mark_persistent(l_USize_HasDiv);
 l_USize_HasLt = _init_l_USize_HasLt();
lean::mark_persistent(l_USize_HasLt);
 l_USize_HasLe = _init_l_USize_HasLe();
lean::mark_persistent(l_USize_HasLe);
 l_USize_Inhabited = _init_l_USize_Inhabited();
 l_USize_Inhabited___boxed = _init_l_USize_Inhabited___boxed();
lean::mark_persistent(l_USize_Inhabited___boxed);
 l_USize_DecidableEq = _init_l_USize_DecidableEq();
lean::mark_persistent(l_USize_DecidableEq);
return w;
}
