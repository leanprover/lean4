// Lean compiler output
// Module: init.lean.ir.instances
// Imports: init.lean.ir.ir
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_ir_blockid_decidable__eq;
obj* l_lean_ir_mk__var__set;
obj* l_lean_ir_var_hashable;
obj* l_lean_ir_blockid_hashable;
extern obj* l_lean_name_decidable__eq;
obj* l_lean_ir_fnid__set;
unsigned char l_lean_ir_id2type(obj*);
unsigned char l_lean_ir_type__has__dec__eq(unsigned char, unsigned char);
obj* l_lean_ir_fnid2string;
obj* l_lean_ir_type2id___main(unsigned char);
obj* l_lean_ir_type2id___main___boxed(obj*);
obj* l_lean_ir_mk__fnid__set;
obj* l_lean_ir_blockid__set;
obj* l_lean_ir_mk__fnid2string;
extern obj* l_lean_name_hashable;
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
unsigned char l_lean_ir_inhabited;
obj* l_lean_ir_mk__context;
unsigned char l_lean_ir_id2type___main(obj*);
obj* l_lean_ir_var_decidable__eq;
obj* l_lean_ir_var2blockid;
obj* l_lean_ir_fnid__has__lt;
obj* l_lean_ir_id2type___boxed(obj*);
obj* l_lean_ir_type__has__dec__eq___boxed(obj*, obj*);
obj* l_lean_ir_blockid__has__lt;
obj* l_lean_ir_type2id(unsigned char);
obj* l_lean_ir_type2id___main(unsigned char x_0) {
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
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_type2id___main(x_1);
return x_2;
}
}
obj* l_lean_ir_type2id(unsigned char x_0) {
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
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_type2id(x_1);
return x_2;
}
}
unsigned char l_lean_ir_id2type___main(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; unsigned char x_8; 
x_7 = lean::mk_nat_obj(2u);
x_8 = lean::nat_dec_eq(x_0, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_10; unsigned char x_11; 
x_10 = lean::mk_nat_obj(3u);
x_11 = lean::nat_dec_eq(x_0, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_13; unsigned char x_14; 
x_13 = lean::mk_nat_obj(4u);
x_14 = lean::nat_dec_eq(x_0, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_16; unsigned char x_17; 
x_16 = lean::mk_nat_obj(5u);
x_17 = lean::nat_dec_eq(x_0, x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_19; unsigned char x_20; 
x_19 = lean::mk_nat_obj(6u);
x_20 = lean::nat_dec_eq(x_0, x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_22; unsigned char x_23; 
x_22 = lean::mk_nat_obj(7u);
x_23 = lean::nat_dec_eq(x_0, x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_25; unsigned char x_26; 
x_25 = lean::mk_nat_obj(8u);
x_26 = lean::nat_dec_eq(x_0, x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_28; unsigned char x_29; 
x_28 = lean::mk_nat_obj(9u);
x_29 = lean::nat_dec_eq(x_0, x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_31; unsigned char x_32; 
x_31 = lean::mk_nat_obj(10u);
x_32 = lean::nat_dec_eq(x_0, x_31);
lean::dec(x_31);
lean::dec(x_0);
if (x_32 == 0)
{
unsigned char x_35; 
x_35 = 11;
return x_35;
}
else
{
unsigned char x_36; 
x_36 = 10;
return x_36;
}
}
else
{
unsigned char x_38; 
lean::dec(x_0);
x_38 = 9;
return x_38;
}
}
else
{
unsigned char x_40; 
lean::dec(x_0);
x_40 = 8;
return x_40;
}
}
else
{
unsigned char x_42; 
lean::dec(x_0);
x_42 = 7;
return x_42;
}
}
else
{
unsigned char x_44; 
lean::dec(x_0);
x_44 = 6;
return x_44;
}
}
else
{
unsigned char x_46; 
lean::dec(x_0);
x_46 = 5;
return x_46;
}
}
else
{
unsigned char x_48; 
lean::dec(x_0);
x_48 = 4;
return x_48;
}
}
else
{
unsigned char x_50; 
lean::dec(x_0);
x_50 = 3;
return x_50;
}
}
else
{
unsigned char x_52; 
lean::dec(x_0);
x_52 = 2;
return x_52;
}
}
else
{
unsigned char x_54; 
lean::dec(x_0);
x_54 = 1;
return x_54;
}
}
else
{
unsigned char x_56; 
lean::dec(x_0);
x_56 = 0;
return x_56;
}
}
}
obj* l_lean_ir_id2type___main___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_lean_ir_id2type___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char l_lean_ir_id2type(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = l_lean_ir_id2type___main(x_0);
return x_1;
}
}
obj* l_lean_ir_id2type___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_lean_ir_id2type(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char l_lean_ir_type__has__dec__eq(unsigned char x_0, unsigned char x_1) {
_start:
{
obj* x_2; obj* x_3; unsigned char x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_type2id___main(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
if (x_4 == 0)
{
unsigned char x_7; 
x_7 = 0;
return x_7;
}
else
{
unsigned char x_8; 
x_8 = 1;
return x_8;
}
}
}
obj* l_lean_ir_type__has__dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; unsigned char x_4; obj* x_5; 
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
obj* _init_l_lean_ir_var_hashable() {
_start:
{
obj* x_0; 
x_0 = l_lean_name_hashable;
lean::inc(x_0);
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
obj* _init_l_lean_ir_blockid_hashable() {
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
obj* _init_l_lean_ir_fnid_hashable() {
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
obj* _init_l_lean_ir_var__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_blockid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_context() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_var2blockid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid2string() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_ir_fnid__set() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
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
unsigned char _init_l_lean_ir_inhabited() {
_start:
{
unsigned char x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_lean_ir_inhabited___boxed() {
_start:
{
unsigned char x_0; obj* x_1; 
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
 l_lean_ir_var_hashable = _init_l_lean_ir_var_hashable();
 l_lean_ir_var_decidable__eq = _init_l_lean_ir_var_decidable__eq();
 l_lean_ir_blockid_hashable = _init_l_lean_ir_blockid_hashable();
 l_lean_ir_blockid_decidable__eq = _init_l_lean_ir_blockid_decidable__eq();
 l_lean_ir_fnid_hashable = _init_l_lean_ir_fnid_hashable();
 l_lean_ir_fnid_decidable__eq = _init_l_lean_ir_fnid_decidable__eq();
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
