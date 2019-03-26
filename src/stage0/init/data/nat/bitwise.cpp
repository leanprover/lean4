// Lean compiler output
// Module: init.data.nat.bitwise
// Imports: init.data.nat.basic init.data.nat.div init.coe
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
obj* l_Nat_bitwise___boxed(obj*, obj*, obj*);
obj* l_Nat_bitwise___main(obj*, obj*, obj*);
obj* l_Nat_lor___closed__1;
obj* l_Nat_lor___lambda__1___boxed(obj*, obj*);
obj* l_Nat_land___lambda__1___boxed(obj*, obj*);
uint8 l_Nat_lor___lambda__1(uint8, uint8);
obj* l_Nat_bitwise___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mod(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Nat_land___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Nat_land___lambda__1(uint8, uint8);
obj* l_Nat_bitwise(obj*, obj*, obj*);
obj* l_Nat_land___closed__1;
obj* l_Nat_land(obj*, obj*);
obj* l_Nat_lor___boxed(obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Nat_lor(obj*, obj*);
obj* l_Nat_bitwise___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_2, x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_14; uint8 x_15; obj* x_17; uint8 x_18; obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_6 = lean::mk_nat_obj(2ul);
x_7 = lean::nat_div(x_1, x_6);
x_8 = lean::nat_div(x_2, x_6);
lean::inc(x_0);
x_10 = l_Nat_bitwise___main(x_0, x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
x_13 = lean::nat_mod(x_1, x_6);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_13);
x_17 = lean::nat_mod(x_2, x_6);
x_18 = lean::nat_dec_eq(x_17, x_14);
lean::dec(x_17);
x_20 = lean::box(x_15);
x_21 = lean::box(x_18);
x_22 = lean::apply_2(x_0, x_20, x_21);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_24; 
x_24 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_24;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_28 = lean::nat_add(x_26, x_14);
lean::dec(x_26);
return x_28;
}
}
else
{
uint8 x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_30 = 1;
x_31 = 0;
x_32 = lean::box(x_30);
x_33 = lean::box(x_31);
x_34 = lean::apply_2(x_0, x_32, x_33);
x_35 = lean::unbox(x_34);
if (x_35 == 0)
{
return x_3;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
else
{
uint8 x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; uint8 x_42; 
x_37 = 0;
x_38 = 1;
x_39 = lean::box(x_37);
x_40 = lean::box(x_38);
x_41 = lean::apply_2(x_0, x_39, x_40);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
return x_3;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
}
obj* l_Nat_bitwise___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_bitwise___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Nat_bitwise(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_bitwise___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Nat_bitwise___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_bitwise(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Nat_land___lambda__1(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
return x_1;
}
}
}
obj* _init_l_Nat_land___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_land___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_Nat_land(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_land___closed__1;
x_3 = l_Nat_bitwise___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Nat_land___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Nat_land___lambda__1(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Nat_land___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_land(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Nat_lor___lambda__1(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* _init_l_Nat_lor___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_lor___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_Nat_lor(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_lor___closed__1;
x_3 = l_Nat_bitwise___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Nat_lor___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Nat_lor___lambda__1(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Nat_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_lor(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_nat_div(obj*);
obj* initialize_init_coe(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_nat_bitwise(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
 l_Nat_land___closed__1 = _init_l_Nat_land___closed__1();
lean::mark_persistent(l_Nat_land___closed__1);
 l_Nat_lor___closed__1 = _init_l_Nat_lor___closed__1();
lean::mark_persistent(l_Nat_lor___closed__1);
return w;
}
