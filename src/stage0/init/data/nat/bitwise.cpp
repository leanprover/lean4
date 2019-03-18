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
obj* l_nat_lor___closed__1;
obj* l_nat_lor___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_nat_bitwise(obj*, obj*, obj*);
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_nat_bitwise___main(obj*, obj*, obj*);
obj* l_nat_bitwise___boxed(obj*, obj*, obj*);
obj* l_nat_land(obj*, obj*);
obj* l_nat_land___boxed(obj*, obj*);
obj* l_nat_lor(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_nat_land___lambda__1___boxed(obj*, obj*);
obj* l_nat_land___closed__1;
uint8 l_nat_lor___lambda__1(uint8, uint8);
uint8 l_nat_land___lambda__1(uint8, uint8);
obj* l_nat_lor___lambda__1___boxed(obj*, obj*);
obj* l_nat_bitwise___main___boxed(obj*, obj*, obj*);
obj* l_nat_bitwise___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::nat_dec_eq(x_2, x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_14; uint8 x_15; obj* x_17; uint8 x_18; 
x_6 = lean::mk_nat_obj(2u);
x_7 = lean::nat_div(x_1, x_6);
x_8 = lean::nat_div(x_2, x_6);
lean::inc(x_0);
x_10 = l_nat_bitwise___main(x_0, x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
x_13 = lean::nat_mod(x_1, x_6);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_13);
x_17 = lean::nat_mod(x_2, x_6);
x_18 = lean::nat_dec_eq(x_17, x_14);
lean::dec(x_17);
if (x_15 == 0)
{
if (x_18 == 0)
{
uint8 x_20; obj* x_21; obj* x_23; uint8 x_24; 
x_20 = 0;
x_21 = lean::box(x_20);
lean::inc(x_21);
x_23 = lean::apply_2(x_0, x_21, x_21);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
obj* x_25; 
x_25 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_25;
}
else
{
obj* x_27; obj* x_29; 
x_27 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_29 = lean::nat_add(x_27, x_14);
lean::dec(x_27);
return x_29;
}
}
else
{
uint8 x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_31 = 0;
x_32 = 1;
x_33 = lean::box(x_31);
x_34 = lean::box(x_32);
x_35 = lean::apply_2(x_0, x_33, x_34);
x_36 = lean::unbox(x_35);
if (x_36 == 0)
{
obj* x_37; 
x_37 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_37;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_41 = lean::nat_add(x_39, x_14);
lean::dec(x_39);
return x_41;
}
}
}
else
{
if (x_18 == 0)
{
uint8 x_43; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_43 = 1;
x_44 = 0;
x_45 = lean::box(x_43);
x_46 = lean::box(x_44);
x_47 = lean::apply_2(x_0, x_45, x_46);
x_48 = lean::unbox(x_47);
if (x_48 == 0)
{
obj* x_49; 
x_49 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_49;
}
else
{
obj* x_51; obj* x_53; 
x_51 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_53 = lean::nat_add(x_51, x_14);
lean::dec(x_51);
return x_53;
}
}
else
{
uint8 x_55; obj* x_56; obj* x_58; uint8 x_59; 
x_55 = 1;
x_56 = lean::box(x_55);
lean::inc(x_56);
x_58 = lean::apply_2(x_0, x_56, x_56);
x_59 = lean::unbox(x_58);
if (x_59 == 0)
{
obj* x_60; 
x_60 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_60;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_64 = lean::nat_add(x_62, x_14);
lean::dec(x_62);
return x_64;
}
}
}
}
else
{
uint8 x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; uint8 x_71; 
x_66 = 1;
x_67 = 0;
x_68 = lean::box(x_66);
x_69 = lean::box(x_67);
x_70 = lean::apply_2(x_0, x_68, x_69);
x_71 = lean::unbox(x_70);
if (x_71 == 0)
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
uint8 x_73; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; uint8 x_78; 
x_73 = 0;
x_74 = 1;
x_75 = lean::box(x_73);
x_76 = lean::box(x_74);
x_77 = lean::apply_2(x_0, x_75, x_76);
x_78 = lean::unbox(x_77);
if (x_78 == 0)
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
obj* l_nat_bitwise___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_nat_bitwise___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_nat_bitwise(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_nat_bitwise___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_nat_bitwise___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_nat_bitwise(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_nat_land___lambda__1(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_0;
}
else
{
return x_1;
}
}
}
obj* _init_l_nat_land___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_land___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_nat_land(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_nat_land___closed__1;
x_3 = l_nat_bitwise___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_nat_land___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_nat_land___lambda__1(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_nat_land___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_land(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_nat_lor___lambda__1(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
return x_1;
}
else
{
return x_0;
}
}
}
obj* _init_l_nat_lor___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_lor___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_nat_lor(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_nat_lor___closed__1;
x_3 = l_nat_bitwise___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_nat_lor___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_nat_lor___lambda__1(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_nat_lor___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_lor(x_0, x_1);
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
 l_nat_land___closed__1 = _init_l_nat_land___closed__1();
lean::mark_persistent(l_nat_land___closed__1);
 l_nat_lor___closed__1 = _init_l_nat_lor___closed__1();
lean::mark_persistent(l_nat_lor___closed__1);
return w;
}
