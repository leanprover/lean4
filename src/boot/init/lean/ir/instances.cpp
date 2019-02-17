// Lean compiler output
// Module: init.lean.ir.instances
// Imports: init.lean.ir.ir
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
obj* l_lean_ir_blockid_decidable__eq;
obj* l_lean_ir_mk__var__set;
obj* l_lean_ir_var_hashable;
obj* l_lean_ir_blockid_hashable;
extern obj* l_lean_name_decidable__eq;
obj* l_lean_ir_fnid__set;
uint8 l_lean_ir_id2type(obj*);
uint8 l_lean_ir_type__has__dec__eq(uint8, uint8);
obj* l_lean_ir_fnid2string;
obj* l_lean_ir_type2id___main(uint8);
obj* l_lean_ir_type2id___main___boxed(obj*);
obj* l_lean_ir_mk__fnid__set;
obj* l_lean_ir_blockid__set;
obj* l_lean_ir_mk__fnid2string;
extern obj* l_lean_name_hashable;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_ir_type2id___boxed(obj*);
obj* l_lean_ir_mk__var2blockid;
obj* l_lean_ir_inhabited___boxed;
obj* l_lean_ir_var__has__lt;
obj* l_lean_ir_context;
obj* l_lean_mk__simple__name(obj*);
obj* l_lean_ir_mk__blockid__set;
obj* l_lean_ir_fnid_decidable__eq;
obj* l_lean_ir_id2type___main___boxed(obj*);
obj* l_lean_ir_var__set;
obj* l_lean_ir_fnid_hashable;
obj* l_lean_ir_has__coe;
uint8 l_lean_ir_inhabited;
obj* l_lean_ir_mk__context;
uint8 l_lean_ir_id2type___main(obj*);
obj* l_lean_ir_var_decidable__eq;
obj* l_lean_ir_var2blockid;
obj* l_lean_ir_fnid__has__lt;
obj* l_lean_ir_id2type___boxed(obj*);
obj* l_lean_ir_type__has__dec__eq___boxed(obj*, obj*);
obj* l_lean_ir_blockid__has__lt;
obj* l_lean_ir_type2id(uint8);
obj* l_lean_ir_type2id___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0u);
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = lean::mk_nat_obj(1u);
return x_2;
}
case 2:
{
obj* x_3; 
x_3 = lean::mk_nat_obj(2u);
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = lean::mk_nat_obj(3u);
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = lean::mk_nat_obj(4u);
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = lean::mk_nat_obj(5u);
return x_6;
}
case 6:
{
obj* x_7; 
x_7 = lean::mk_nat_obj(6u);
return x_7;
}
case 7:
{
obj* x_8; 
x_8 = lean::mk_nat_obj(7u);
return x_8;
}
case 8:
{
obj* x_9; 
x_9 = lean::mk_nat_obj(8u);
return x_9;
}
case 9:
{
obj* x_10; 
x_10 = lean::mk_nat_obj(9u);
return x_10;
}
case 10:
{
obj* x_11; 
x_11 = lean::mk_nat_obj(10u);
return x_11;
}
default:
{
obj* x_12; 
x_12 = lean::mk_nat_obj(11u);
return x_12;
}
}
}
}
obj* l_lean_ir_type2id___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_type2id___main(x_1);
return x_2;
}
}
obj* l_lean_ir_type2id(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* l_lean_ir_type2id___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_type2id(x_1);
return x_2;
}
}
uint8 l_lean_ir_id2type___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(2u);
x_6 = lean::nat_dec_eq(x_0, x_5);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(3u);
x_8 = lean::nat_dec_eq(x_0, x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(4u);
x_10 = lean::nat_dec_eq(x_0, x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(5u);
x_12 = lean::nat_dec_eq(x_0, x_11);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::mk_nat_obj(6u);
x_14 = lean::nat_dec_eq(x_0, x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::mk_nat_obj(7u);
x_16 = lean::nat_dec_eq(x_0, x_15);
if (x_16 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(8u);
x_18 = lean::nat_dec_eq(x_0, x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = lean::mk_nat_obj(9u);
x_20 = lean::nat_dec_eq(x_0, x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::mk_nat_obj(10u);
x_22 = lean::nat_dec_eq(x_0, x_21);
lean::dec(x_0);
if (x_22 == 0)
{
uint8 x_24; 
x_24 = 11;
return x_24;
}
else
{
uint8 x_25; 
x_25 = 10;
return x_25;
}
}
else
{
uint8 x_27; 
lean::dec(x_0);
x_27 = 9;
return x_27;
}
}
else
{
uint8 x_29; 
lean::dec(x_0);
x_29 = 8;
return x_29;
}
}
else
{
uint8 x_31; 
lean::dec(x_0);
x_31 = 7;
return x_31;
}
}
else
{
uint8 x_33; 
lean::dec(x_0);
x_33 = 6;
return x_33;
}
}
else
{
uint8 x_35; 
lean::dec(x_0);
x_35 = 5;
return x_35;
}
}
else
{
uint8 x_37; 
lean::dec(x_0);
x_37 = 4;
return x_37;
}
}
else
{
uint8 x_39; 
lean::dec(x_0);
x_39 = 3;
return x_39;
}
}
else
{
uint8 x_41; 
lean::dec(x_0);
x_41 = 2;
return x_41;
}
}
else
{
uint8 x_43; 
lean::dec(x_0);
x_43 = 1;
return x_43;
}
}
else
{
uint8 x_45; 
lean::dec(x_0);
x_45 = 0;
return x_45;
}
}
}
obj* l_lean_ir_id2type___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_id2type___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_lean_ir_id2type(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_id2type___main(x_0);
return x_1;
}
}
obj* l_lean_ir_id2type___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_id2type(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_lean_ir_type__has__dec__eq(uint8 x_0, uint8 x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_type2id___main(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
if (x_4 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
obj* l_lean_ir_type__has__dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_type__has__dec__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_lean_ir_has__coe() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_mk__simple__name), 1, 0);
return x_0;
}
}
obj* _init_l_lean_ir_var__has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid__has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid__has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_var_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_var_hashable() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid_hashable() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid_hashable() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_var__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_context() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_var2blockid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid2string() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__var__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__blockid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__var2blockid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__context() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__fnid2string() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_mk__fnid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 _init_l_lean_ir_inhabited() {
_start:
{
uint8 x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_lean_ir_inhabited___boxed() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = l_lean_ir_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
void initialize_init_lean_ir_ir();
static bool _G_initialized = false;
void initialize_init_lean_ir_instances() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_ir();
 l_lean_ir_has__coe = _init_l_lean_ir_has__coe();
 l_lean_ir_var__has__lt = _init_l_lean_ir_var__has__lt();
 l_lean_ir_blockid__has__lt = _init_l_lean_ir_blockid__has__lt();
 l_lean_ir_fnid__has__lt = _init_l_lean_ir_fnid__has__lt();
 l_lean_ir_var_decidable__eq = _init_l_lean_ir_var_decidable__eq();
 l_lean_ir_var_hashable = _init_l_lean_ir_var_hashable();
 l_lean_ir_blockid_decidable__eq = _init_l_lean_ir_blockid_decidable__eq();
 l_lean_ir_blockid_hashable = _init_l_lean_ir_blockid_hashable();
 l_lean_ir_fnid_decidable__eq = _init_l_lean_ir_fnid_decidable__eq();
 l_lean_ir_fnid_hashable = _init_l_lean_ir_fnid_hashable();
 l_lean_ir_var__set = _init_l_lean_ir_var__set();
 l_lean_ir_blockid__set = _init_l_lean_ir_blockid__set();
 l_lean_ir_context = _init_l_lean_ir_context();
 l_lean_ir_var2blockid = _init_l_lean_ir_var2blockid();
 l_lean_ir_fnid2string = _init_l_lean_ir_fnid2string();
 l_lean_ir_fnid__set = _init_l_lean_ir_fnid__set();
 l_lean_ir_mk__var__set = _init_l_lean_ir_mk__var__set();
 l_lean_ir_mk__blockid__set = _init_l_lean_ir_mk__blockid__set();
 l_lean_ir_mk__var2blockid = _init_l_lean_ir_mk__var2blockid();
 l_lean_ir_mk__context = _init_l_lean_ir_mk__context();
 l_lean_ir_mk__fnid2string = _init_l_lean_ir_mk__fnid2string();
 l_lean_ir_mk__fnid__set = _init_l_lean_ir_mk__fnid__set();
 l_lean_ir_inhabited = _init_l_lean_ir_inhabited();
 l_lean_ir_inhabited___boxed = _init_l_lean_ir_inhabited___boxed();
}
