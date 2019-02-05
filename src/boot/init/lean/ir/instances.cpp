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
obj* l_lean_ir_mk__fnid__set;
obj* l_lean_mk__simple__name(obj*);
obj* l_lean_ir_context;
unsigned char l_lean_ir_id2type(obj*);
obj* l_lean_ir_blockid_hashable;
obj* l_lean_ir_var_decidable__eq;
obj* l_lean_ir_fnid_hashable;
obj* l_lean_ir_id2type___main___boxed(obj*);
obj* l_lean_ir_mk__blockid__set;
obj* l_lean_ir_blockid__has__lt;
obj* l_lean_ir_type__has__dec__eq(unsigned char, unsigned char);
obj* l_lean_ir_type2id(unsigned char);
obj* l_lean_ir_var_hashable;
extern obj* l_lean_name_hashable;
obj* l_lean_ir_type2id___main___boxed(obj*);
obj* l_lean_ir_fnid2string;
obj* l_lean_ir_type2id___main(unsigned char);
obj* l_lean_ir_blockid__set;
unsigned char l_lean_ir_id2type___main(obj*);
obj* l_lean_ir_inhabited___boxed;
obj* l_lean_ir_type__has__dec__eq___boxed(obj*, obj*);
extern obj* l_lean_name_decidable__eq;
obj* l_lean_ir_mk__context;
unsigned char l_lean_ir_inhabited;
obj* l_lean_ir_id2type___boxed(obj*);
obj* l_lean_ir_fnid__has__lt;
obj* l_lean_ir_blockid_decidable__eq;
obj* l_lean_ir_mk__var__set;
obj* l_lean_ir_mk__fnid2string;
obj* l_lean_ir_type2id___boxed(obj*);
obj* l_lean_ir_var2blockid;
obj* l_lean_ir_var__has__lt;
obj* l_lean_ir_fnid__set;
obj* l_lean_ir_var__set;
obj* l_lean_ir_fnid_decidable__eq;
obj* l_lean_ir_mk__var2blockid;
obj* l_lean_ir_has__coe;
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
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_dec_eq(x_0, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(2u);
x_10 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_10);
x_13 = lean::mk_nat_obj(3u);
x_14 = lean::nat_dec_eq(x_0, x_13);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_14);
x_17 = lean::mk_nat_obj(4u);
x_18 = lean::nat_dec_eq(x_0, x_17);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_18);
x_21 = lean::mk_nat_obj(5u);
x_22 = lean::nat_dec_eq(x_0, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_22);
x_25 = lean::mk_nat_obj(6u);
x_26 = lean::nat_dec_eq(x_0, x_25);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_26);
x_29 = lean::mk_nat_obj(7u);
x_30 = lean::nat_dec_eq(x_0, x_29);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_30);
x_33 = lean::mk_nat_obj(8u);
x_34 = lean::nat_dec_eq(x_0, x_33);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_34);
x_37 = lean::mk_nat_obj(9u);
x_38 = lean::nat_dec_eq(x_0, x_37);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_38);
x_41 = lean::mk_nat_obj(10u);
x_42 = lean::nat_dec_eq(x_0, x_41);
lean::dec(x_41);
lean::dec(x_0);
if (lean::obj_tag(x_42) == 0)
{
unsigned char x_46; 
lean::dec(x_42);
x_46 = 11;
return x_46;
}
else
{
unsigned char x_48; 
lean::dec(x_42);
x_48 = 10;
return x_48;
}
}
else
{
unsigned char x_51; 
lean::dec(x_0);
lean::dec(x_38);
x_51 = 9;
return x_51;
}
}
else
{
unsigned char x_54; 
lean::dec(x_0);
lean::dec(x_34);
x_54 = 8;
return x_54;
}
}
else
{
unsigned char x_57; 
lean::dec(x_0);
lean::dec(x_30);
x_57 = 7;
return x_57;
}
}
else
{
unsigned char x_60; 
lean::dec(x_0);
lean::dec(x_26);
x_60 = 6;
return x_60;
}
}
else
{
unsigned char x_63; 
lean::dec(x_0);
lean::dec(x_22);
x_63 = 5;
return x_63;
}
}
else
{
unsigned char x_66; 
lean::dec(x_18);
lean::dec(x_0);
x_66 = 4;
return x_66;
}
}
else
{
unsigned char x_69; 
lean::dec(x_14);
lean::dec(x_0);
x_69 = 3;
return x_69;
}
}
else
{
unsigned char x_72; 
lean::dec(x_10);
lean::dec(x_0);
x_72 = 2;
return x_72;
}
}
else
{
unsigned char x_75; 
lean::dec(x_6);
lean::dec(x_0);
x_75 = 1;
return x_75;
}
}
else
{
unsigned char x_78; 
lean::dec(x_0);
lean::dec(x_2);
x_78 = 0;
return x_78;
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
obj* l_lean_ir_type__has__dec__eq(unsigned char x_0, unsigned char x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_type2id___main(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_type__has__dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_type__has__dec__eq(x_2, x_3);
return x_4;
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
