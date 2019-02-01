// Lean compiler output
// Module: init.lean.ir.instances
// Imports: init.lean.ir.ir
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s2_ir_s13_mk__fnid__set;
obj* _l_s4_lean_s16_mk__simple__name(obj*);
obj* _l_s4_lean_s2_ir_s7_context;
unsigned char _l_s4_lean_s2_ir_s7_id2type(obj*);
obj* _l_s4_lean_s2_ir_s7_blockid_s8_hashable;
obj* _l_s4_lean_s2_ir_s3_var_s13_decidable__eq;
obj* _l_s4_lean_s2_ir_s4_fnid_s8_hashable;
obj* _l_s4_lean_s2_ir_s7_id2type_s6___main_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s16_mk__blockid__set;
obj* _l_s4_lean_s2_ir_s16_blockid__has__lt;
obj* _l_s4_lean_s2_ir_s18_type__has__dec__eq(unsigned char, unsigned char);
obj* _l_s4_lean_s2_ir_s7_type2id(unsigned char);
obj* _l_s4_lean_s2_ir_s3_var_s8_hashable;
obj* _l_s4_lean_s4_name_s8_hashable;
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s11_fnid2string;
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main(unsigned char);
obj* _l_s4_lean_s2_ir_s12_blockid__set;
unsigned char _l_s4_lean_s2_ir_s7_id2type_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s9_inhabited_s7___boxed;
obj* _l_s4_lean_s2_ir_s18_type__has__dec__eq_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s4_name_s13_decidable__eq;
obj* _l_s4_lean_s2_ir_s11_mk__context;
unsigned char _l_s4_lean_s2_ir_s9_inhabited;
obj* _l_s4_lean_s2_ir_s7_id2type_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s13_fnid__has__lt;
obj* _l_s4_lean_s2_ir_s7_blockid_s13_decidable__eq;
obj* _l_s4_lean_s2_ir_s12_mk__var__set;
obj* _l_s4_lean_s2_ir_s15_mk__fnid2string;
obj* _l_s4_lean_s2_ir_s7_type2id_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s11_var2blockid;
obj* _l_s4_lean_s2_ir_s12_var__has__lt;
obj* _l_s4_lean_s2_ir_s9_fnid__set;
obj* _l_s4_lean_s2_ir_s8_var__set;
obj* _l_s4_lean_s2_ir_s4_fnid_s13_decidable__eq;
obj* _l_s4_lean_s2_ir_s15_mk__var2blockid;
obj* _l_s4_lean_s2_ir_s8_has__coe;
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main(unsigned char x_0) {
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
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s7_type2id(unsigned char x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s7_type2id_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s7_type2id(x_1);
return x_2;
}
}
unsigned char _l_s4_lean_s2_ir_s7_id2type_s6___main(obj* x_0) {
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
obj* _l_s4_lean_s2_ir_s7_id2type_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_lean_s2_ir_s7_id2type_s6___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char _l_s4_lean_s2_ir_s7_id2type(obj* x_0) {
{
unsigned char x_1; 
x_1 = _l_s4_lean_s2_ir_s7_id2type_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s7_id2type_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s4_lean_s2_ir_s7_id2type(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s18_type__has__dec__eq(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
x_3 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s18_type__has__dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s4_lean_s2_ir_s18_type__has__dec__eq(x_2, x_3);
return x_4;
}
}
obj* _init__l_s4_lean_s2_ir_s8_has__coe() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s16_mk__simple__name), 1, 0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s12_var__has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s16_blockid__has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s13_fnid__has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_var_s8_hashable() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s8_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_var_s13_decidable__eq() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s13_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s7_blockid_s8_hashable() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s8_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s7_blockid_s13_decidable__eq() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s13_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s4_fnid_s8_hashable() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s8_hashable;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s4_fnid_s13_decidable__eq() {
{
obj* x_0; 
x_0 = _l_s4_lean_s4_name_s13_decidable__eq;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s8_var__set() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s12_blockid__set() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s7_context() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s11_var2blockid() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s11_fnid2string() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s9_fnid__set() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s12_mk__var__set() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s16_mk__blockid__set() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s15_mk__var2blockid() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s11_mk__context() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s15_mk__fnid2string() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s13_mk__fnid__set() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
unsigned char _init__l_s4_lean_s2_ir_s9_inhabited() {
{
unsigned char x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s9_inhabited_s7___boxed() {
{
unsigned char x_0; obj* x_1; 
x_0 = _l_s4_lean_s2_ir_s9_inhabited;
x_1 = lean::box(x_0);
return x_1;
}
}
void _l_initialize__l_s4_init_s4_lean_s2_ir_s2_ir();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s2_ir_s9_instances() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s2_ir_s2_ir();
 _l_s4_lean_s2_ir_s8_has__coe = _init__l_s4_lean_s2_ir_s8_has__coe();
 _l_s4_lean_s2_ir_s12_var__has__lt = _init__l_s4_lean_s2_ir_s12_var__has__lt();
 _l_s4_lean_s2_ir_s16_blockid__has__lt = _init__l_s4_lean_s2_ir_s16_blockid__has__lt();
 _l_s4_lean_s2_ir_s13_fnid__has__lt = _init__l_s4_lean_s2_ir_s13_fnid__has__lt();
 _l_s4_lean_s2_ir_s3_var_s8_hashable = _init__l_s4_lean_s2_ir_s3_var_s8_hashable();
 _l_s4_lean_s2_ir_s3_var_s13_decidable__eq = _init__l_s4_lean_s2_ir_s3_var_s13_decidable__eq();
 _l_s4_lean_s2_ir_s7_blockid_s8_hashable = _init__l_s4_lean_s2_ir_s7_blockid_s8_hashable();
 _l_s4_lean_s2_ir_s7_blockid_s13_decidable__eq = _init__l_s4_lean_s2_ir_s7_blockid_s13_decidable__eq();
 _l_s4_lean_s2_ir_s4_fnid_s8_hashable = _init__l_s4_lean_s2_ir_s4_fnid_s8_hashable();
 _l_s4_lean_s2_ir_s4_fnid_s13_decidable__eq = _init__l_s4_lean_s2_ir_s4_fnid_s13_decidable__eq();
 _l_s4_lean_s2_ir_s8_var__set = _init__l_s4_lean_s2_ir_s8_var__set();
 _l_s4_lean_s2_ir_s12_blockid__set = _init__l_s4_lean_s2_ir_s12_blockid__set();
 _l_s4_lean_s2_ir_s7_context = _init__l_s4_lean_s2_ir_s7_context();
 _l_s4_lean_s2_ir_s11_var2blockid = _init__l_s4_lean_s2_ir_s11_var2blockid();
 _l_s4_lean_s2_ir_s11_fnid2string = _init__l_s4_lean_s2_ir_s11_fnid2string();
 _l_s4_lean_s2_ir_s9_fnid__set = _init__l_s4_lean_s2_ir_s9_fnid__set();
 _l_s4_lean_s2_ir_s12_mk__var__set = _init__l_s4_lean_s2_ir_s12_mk__var__set();
 _l_s4_lean_s2_ir_s16_mk__blockid__set = _init__l_s4_lean_s2_ir_s16_mk__blockid__set();
 _l_s4_lean_s2_ir_s15_mk__var2blockid = _init__l_s4_lean_s2_ir_s15_mk__var2blockid();
 _l_s4_lean_s2_ir_s11_mk__context = _init__l_s4_lean_s2_ir_s11_mk__context();
 _l_s4_lean_s2_ir_s15_mk__fnid2string = _init__l_s4_lean_s2_ir_s15_mk__fnid2string();
 _l_s4_lean_s2_ir_s13_mk__fnid__set = _init__l_s4_lean_s2_ir_s13_mk__fnid__set();
 _l_s4_lean_s2_ir_s9_inhabited = _init__l_s4_lean_s2_ir_s9_inhabited();
 _l_s4_lean_s2_ir_s9_inhabited_s7___boxed = _init__l_s4_lean_s2_ir_s9_inhabited_s7___boxed();
}
