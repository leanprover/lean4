// Lean compiler output
// Module: init.lean.ir.type_check
// Imports: init.lean.ir.instances init.lean.ir.format init.control.combinators
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s16_type__checker__m;
obj* _l_s4_lean_s2_ir_s11_check__type_s11___closed__2;
obj* _l_s4_lean_s2_ir_s4_decl_s12_infer__types(obj*, obj*, obj*);
unsigned char _l_s4_lean_s2_ir_s26_valid__assign__unop__types(unsigned char, unsigned char, unsigned char);
obj* _l_s4_lean_s2_ir_s19_check__result__type_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s12_infer__types(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_check__type(obj*, unsigned char, obj*, obj*);
obj* _l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2(obj*, obj*);
unsigned char _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__1(obj*, obj*, unsigned char);
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s4_decl_s5_check(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__5;
obj* _l_s4_lean_s2_ir_s17_check__arg__types(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__1;
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s4_type_s10_to__format_s6___main(unsigned char);
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
obj* _l_s4_lean_s2_ir_s16_type__checker__m_s3_run_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__2_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_type__check_s11___closed__1;
obj* _l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_type__check(obj*, obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_match__type(obj*, unsigned char, unsigned char, obj*, obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2(obj*, obj*, unsigned char);
obj* _l_s4_lean_s2_ir_s17_check__arg__types_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(obj*);
obj* _l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__4;
obj* _l_s4_lean_s2_ir_s7_literal_s5_check_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s10_terminator_s5_check_s11___closed__1;
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s15_is__bitwise__ty_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s11_check__type_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2;
obj* _l_s4_lean_s2_ir_s27_valid__assign__binop__types_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__4;
obj* _l_s4_lean_s2_ir_s12_infer__types(obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_get__type(obj*, obj*, obj*);
unsigned char _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty(unsigned char);
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main(unsigned char);
obj* _l_s4_lean_s2_ir_s10_terminator_s5_check(obj*, obj*, obj*);
obj* _l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s16_type__checker__m_s3_run(obj*);
obj* _l_s4_lean_s2_ir_s21_is__signed__arith__ty_s7___boxed(obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s5_check_s6___main_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__2;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__3;
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4;
obj* _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__3;
obj* _l_s4_lean_s2_ir_s7_literal_s5_check(obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s19_check__result__type(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s16_is__bitshift__ty_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s16_invalid__literal(obj*);
obj* _l_s4_lean_s2_ir_s6_header_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_phi_s5_check_s9___spec__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2;
unsigned char _l_s4_lean_s2_ir_s15_is__bitwise__ty(unsigned char);
obj* _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_block_s5_check(obj*, obj*, obj*);
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_get__type_s11___closed__1;
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main_s9___spec__4(obj*);
unsigned char _l_s4_lean_s2_ir_s21_is__signed__arith__ty(unsigned char);
obj* _l_s4_lean_s2_ir_s3_phi_s5_check(obj*, obj*, obj*);
unsigned char _l_s4_lean_s2_ir_s16_is__bitshift__ty(unsigned char);
obj* _l_s4_lean_s2_ir_s4_decl_s5_check_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_set__type(obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_get__decl(obj*, obj*, obj*);
obj* _l_s3_int_s4_zero;
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_arg_s12_infer__types(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_block_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__2;
obj* _l_s4_lean_s2_ir_s11_mk__context;
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__2(unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__1;
obj* _l_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s18_set__result__types_s6___main(obj*, obj*, obj*, obj*);
unsigned char _l_s4_lean_s2_ir_s13_is__arith__ty(unsigned char);
obj* _l_s4_lean_s2_ir_s10_terminator_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s9_set__type_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_block_s12_infer__types(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_phi_s12_infer__types(obj*, obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s13_is__arith__ty_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main(obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__1;
obj* _l_s4_lean_s2_ir_s5_instr_s5_check(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_check__type_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_match__type_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s18_set__result__types(obj*, obj*, obj*, obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(obj*, obj*, unsigned char);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s2_ir_s15_check__ne__type(obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s9_get__decl_s11___closed__1;
unsigned char _l_s4_lean_s2_ir_s27_valid__assign__binop__types(unsigned char, unsigned char, unsigned char, unsigned char);
obj* _l_s4_lean_s2_ir_s3_phi_s10_to__format_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s15_check__ne__type_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(obj*);
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__1(obj*, obj*);
obj* _l_s4_list_s6_length_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
obj* _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__2;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2_s11___closed__1;
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2_s7___boxed(obj*, obj*, obj*);
unsigned char _l_s4_lean_s2_ir_s21_is__signed__arith__ty(unsigned char x_0) {
{

switch (x_0) {
case 0:
{
unsigned char x_1; 
x_1 = 0;
return x_1;
}
case 1:
{
unsigned char x_2; 
x_2 = 0;
return x_2;
}
case 2:
{
unsigned char x_3; 
x_3 = 0;
return x_3;
}
case 3:
{
unsigned char x_4; 
x_4 = 0;
return x_4;
}
case 4:
{
unsigned char x_5; 
x_5 = 0;
return x_5;
}
case 5:
{
unsigned char x_6; 
x_6 = 0;
return x_6;
}
case 6:
{
unsigned char x_7; 
x_7 = 1;
return x_7;
}
case 7:
{
unsigned char x_8; 
x_8 = 1;
return x_8;
}
case 8:
{
unsigned char x_9; 
x_9 = 1;
return x_9;
}
case 9:
{
unsigned char x_10; 
x_10 = 1;
return x_10;
}
case 10:
{
unsigned char x_11; 
x_11 = 1;
return x_11;
}
default:
{
unsigned char x_12; 
x_12 = 0;
return x_12;
}
}
}
}
obj* _l_s4_lean_s2_ir_s21_is__signed__arith__ty_s7___boxed(obj* x_0) {
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s21_is__signed__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s2_ir_s13_is__arith__ty(unsigned char x_0) {
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
x_2 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_6; 
lean::dec(x_3);
x_6 = 1;
return x_6;
}
else
{
unsigned char x_8; 
lean::dec(x_3);
x_8 = 0;
return x_8;
}
}
}
obj* _init__l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1() {
{
unsigned char x_0; obj* x_1; 
x_0 = 0;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s13_is__arith__ty_s7___boxed(obj* x_0) {
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s13_is__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty(unsigned char x_0) {
{
unsigned char x_1; 
x_1 = _l_s4_lean_s2_ir_s13_is__arith__ty(x_0);
if (x_1 == 0)
{

if (x_1 == 0)
{

return x_1;
}
else
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
x_3 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1;
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_4) == 0)
{

lean::dec(x_4);
return x_1;
}
else
{
unsigned char x_8; 
lean::dec(x_4);
x_8 = 0;
return x_8;
}
}
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
x_10 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2;
x_11 = lean::nat_dec_eq(x_9, x_10);
if (lean::obj_tag(x_11) == 0)
{

lean::dec(x_11);
if (x_1 == 0)
{

lean::dec(x_9);
return x_1;
}
else
{
obj* x_14; obj* x_15; 
x_14 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1;
x_15 = lean::nat_dec_eq(x_9, x_14);
lean::dec(x_9);
if (lean::obj_tag(x_15) == 0)
{

lean::dec(x_15);
return x_1;
}
else
{
unsigned char x_19; 
lean::dec(x_15);
x_19 = 0;
return x_19;
}
}
}
else
{
unsigned char x_22; 
lean::dec(x_11);
lean::dec(x_9);
x_22 = 0;
return x_22;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1() {
{
unsigned char x_0; obj* x_1; 
x_0 = 10;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2() {
{
unsigned char x_0; obj* x_1; 
x_0 = 9;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s7___boxed(obj* x_0) {
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s2_ir_s15_is__bitwise__ty(unsigned char x_0) {
{

switch (x_0) {
case 0:
{
unsigned char x_1; 
x_1 = 1;
return x_1;
}
case 1:
{
unsigned char x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
unsigned char x_3; 
x_3 = 1;
return x_3;
}
case 3:
{
unsigned char x_4; 
x_4 = 1;
return x_4;
}
case 4:
{
unsigned char x_5; 
x_5 = 1;
return x_5;
}
case 5:
{
unsigned char x_6; 
x_6 = 1;
return x_6;
}
case 6:
{
unsigned char x_7; 
x_7 = 0;
return x_7;
}
case 7:
{
unsigned char x_8; 
x_8 = 0;
return x_8;
}
case 8:
{
unsigned char x_9; 
x_9 = 0;
return x_9;
}
case 9:
{
unsigned char x_10; 
x_10 = 0;
return x_10;
}
case 10:
{
unsigned char x_11; 
x_11 = 0;
return x_11;
}
default:
{
unsigned char x_12; 
x_12 = 1;
return x_12;
}
}
}
}
obj* _l_s4_lean_s2_ir_s15_is__bitwise__ty_s7___boxed(obj* x_0) {
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s15_is__bitwise__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s2_ir_s16_is__bitshift__ty(unsigned char x_0) {
{

switch (x_0) {
case 0:
{
unsigned char x_1; 
x_1 = 0;
return x_1;
}
case 1:
{
unsigned char x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
unsigned char x_3; 
x_3 = 1;
return x_3;
}
case 3:
{
unsigned char x_4; 
x_4 = 1;
return x_4;
}
case 4:
{
unsigned char x_5; 
x_5 = 1;
return x_5;
}
case 5:
{
unsigned char x_6; 
x_6 = 1;
return x_6;
}
case 6:
{
unsigned char x_7; 
x_7 = 1;
return x_7;
}
case 7:
{
unsigned char x_8; 
x_8 = 1;
return x_8;
}
case 8:
{
unsigned char x_9; 
x_9 = 1;
return x_9;
}
case 9:
{
unsigned char x_10; 
x_10 = 0;
return x_10;
}
case 10:
{
unsigned char x_11; 
x_11 = 0;
return x_11;
}
default:
{
unsigned char x_12; 
x_12 = 0;
return x_12;
}
}
}
}
obj* _l_s4_lean_s2_ir_s16_is__bitshift__ty_s7___boxed(obj* x_0) {
{
unsigned char x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s16_is__bitshift__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s2_ir_s26_valid__assign__unop__types(unsigned char x_0, unsigned char x_1, unsigned char x_2) {
{
unsigned char x_3; unsigned char x_5; unsigned char x_7; unsigned char x_9; unsigned char x_11; 
switch (x_0) {
case 0:
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_14 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_14);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
unsigned char x_19; 
lean::dec(x_15);
x_19 = 0;
return x_19;
}
else
{
unsigned char x_21; 
lean::dec(x_15);
x_21 = _l_s4_lean_s2_ir_s15_is__bitwise__ty(x_2);
return x_21;
}
}
case 1:
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_23 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
lean::dec(x_22);
if (lean::obj_tag(x_24) == 0)
{
unsigned char x_28; 
lean::dec(x_24);
x_28 = 0;
return x_28;
}
else
{
unsigned char x_30; 
lean::dec(x_24);
x_30 = _l_s4_lean_s2_ir_s21_is__signed__arith__ty(x_2);
return x_30;
}
}
case 2:
{
unsigned char x_31; 
x_31 = 0;
x_3 = x_31;
goto lbl_4;
}
case 3:
{
unsigned char x_32; 
x_32 = 0;
x_3 = x_32;
goto lbl_4;
}
case 4:
{
unsigned char x_33; 
x_33 = 0;
x_5 = x_33;
goto lbl_6;
}
case 5:
{
unsigned char x_34; 
x_34 = 0;
x_5 = x_34;
goto lbl_6;
}
case 6:
{
unsigned char x_35; 
x_35 = 0;
x_5 = x_35;
goto lbl_6;
}
case 7:
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_37 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_38 = lean::nat_dec_eq(x_36, x_37);
lean::dec(x_36);
if (lean::obj_tag(x_38) == 0)
{
unsigned char x_41; 
lean::dec(x_38);
x_41 = 1;
return x_41;
}
else
{
unsigned char x_43; 
lean::dec(x_38);
x_43 = 0;
return x_43;
}
}
case 8:
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_45 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_46 = lean::nat_dec_eq(x_44, x_45);
lean::dec(x_44);
if (lean::obj_tag(x_46) == 0)
{
unsigned char x_49; 
lean::dec(x_46);
x_49 = 0;
return x_49;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_46);
x_51 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_52 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
x_53 = lean::nat_dec_eq(x_51, x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_53);
x_55 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4;
x_56 = lean::nat_dec_eq(x_51, x_55);
lean::dec(x_51);
if (lean::obj_tag(x_56) == 0)
{
unsigned char x_59; 
lean::dec(x_56);
x_59 = 0;
return x_59;
}
else
{
unsigned char x_61; 
lean::dec(x_56);
x_61 = 1;
return x_61;
}
}
else
{
unsigned char x_64; 
lean::dec(x_51);
lean::dec(x_53);
x_64 = 1;
return x_64;
}
}
}
case 9:
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_66 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_67 = lean::nat_dec_eq(x_65, x_66);
lean::dec(x_65);
if (lean::obj_tag(x_67) == 0)
{
unsigned char x_70; 
lean::dec(x_67);
x_70 = 0;
return x_70;
}
else
{
obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_67);
x_72 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_73 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
x_74 = lean::nat_dec_eq(x_72, x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_77; 
lean::dec(x_74);
x_76 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4;
x_77 = lean::nat_dec_eq(x_72, x_76);
lean::dec(x_72);
if (lean::obj_tag(x_77) == 0)
{
unsigned char x_80; 
lean::dec(x_77);
x_80 = 0;
return x_80;
}
else
{
unsigned char x_82; 
lean::dec(x_77);
x_82 = 1;
return x_82;
}
}
else
{
unsigned char x_85; 
lean::dec(x_74);
lean::dec(x_72);
x_85 = 1;
return x_85;
}
}
}
case 10:
{
unsigned char x_86; 
x_86 = 0;
x_7 = x_86;
goto lbl_8;
}
case 11:
{
unsigned char x_87; 
x_87 = 0;
x_7 = x_87;
goto lbl_8;
}
case 12:
{
unsigned char x_88; 
x_88 = 0;
x_9 = x_88;
goto lbl_10;
}
case 13:
{
unsigned char x_89; 
x_89 = 0;
x_9 = x_89;
goto lbl_10;
}
case 14:
{
unsigned char x_90; 
x_90 = 0;
x_9 = x_90;
goto lbl_10;
}
case 15:
{
obj* x_91; obj* x_92; obj* x_93; 
x_91 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_92 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_93 = lean::nat_dec_eq(x_91, x_92);
lean::dec(x_91);
if (lean::obj_tag(x_93) == 0)
{
unsigned char x_97; 
lean::dec(x_93);
lean::dec(x_92);
x_97 = 0;
return x_97;
}
else
{
obj* x_99; obj* x_100; 
lean::dec(x_93);
x_99 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_100 = lean::nat_dec_eq(x_99, x_92);
lean::dec(x_99);
if (lean::obj_tag(x_100) == 0)
{
unsigned char x_103; 
lean::dec(x_100);
x_103 = 0;
return x_103;
}
else
{
unsigned char x_105; 
lean::dec(x_100);
x_105 = 1;
return x_105;
}
}
}
case 16:
{
unsigned char x_106; 
x_106 = 0;
x_11 = x_106;
goto lbl_12;
}
default:
{
unsigned char x_107; 
x_107 = 0;
x_11 = x_107;
goto lbl_12;
}
}
lbl_4:
{
obj* x_108; obj* x_109; obj* x_110; 
x_108 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_109 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_110 = lean::nat_dec_eq(x_108, x_109);
lean::dec(x_109);
if (lean::obj_tag(x_110) == 0)
{
unsigned char x_114; 
lean::dec(x_110);
lean::dec(x_108);
x_114 = 0;
return x_114;
}
else
{
obj* x_116; obj* x_117; 
lean::dec(x_110);
x_116 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_117 = lean::nat_dec_eq(x_108, x_116);
lean::dec(x_108);
if (lean::obj_tag(x_117) == 0)
{
unsigned char x_120; 
lean::dec(x_117);
x_120 = 0;
return x_120;
}
else
{
unsigned char x_122; 
lean::dec(x_117);
x_122 = 1;
return x_122;
}
}
}
lbl_6:
{
obj* x_123; obj* x_124; obj* x_125; 
x_123 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_124 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_125 = lean::nat_dec_eq(x_123, x_124);
lean::dec(x_123);
if (lean::obj_tag(x_125) == 0)
{
unsigned char x_128; 
lean::dec(x_125);
x_128 = 0;
return x_128;
}
else
{
obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_125);
x_130 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_131 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_132 = lean::nat_dec_eq(x_130, x_131);
lean::dec(x_130);
if (lean::obj_tag(x_132) == 0)
{
unsigned char x_135; 
lean::dec(x_132);
x_135 = 0;
return x_135;
}
else
{
unsigned char x_137; 
lean::dec(x_132);
x_137 = 1;
return x_137;
}
}
}
lbl_8:
{
obj* x_138; obj* x_139; obj* x_140; 
x_138 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_139 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_140 = lean::nat_dec_eq(x_138, x_139);
lean::dec(x_138);
if (lean::obj_tag(x_140) == 0)
{
unsigned char x_144; 
lean::dec(x_140);
lean::dec(x_139);
x_144 = 0;
return x_144;
}
else
{
obj* x_146; obj* x_147; 
lean::dec(x_140);
x_146 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_147 = lean::nat_dec_eq(x_146, x_139);
lean::dec(x_146);
if (lean::obj_tag(x_147) == 0)
{
unsigned char x_150; 
lean::dec(x_147);
x_150 = 0;
return x_150;
}
else
{
unsigned char x_152; 
lean::dec(x_147);
x_152 = 1;
return x_152;
}
}
}
lbl_10:
{
obj* x_153; obj* x_154; obj* x_155; 
x_153 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_154 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2;
x_155 = lean::nat_dec_eq(x_153, x_154);
lean::dec(x_153);
if (lean::obj_tag(x_155) == 0)
{
unsigned char x_158; 
lean::dec(x_155);
x_158 = 0;
return x_158;
}
else
{
obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_155);
x_160 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_161 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_162 = lean::nat_dec_eq(x_160, x_161);
lean::dec(x_160);
if (lean::obj_tag(x_162) == 0)
{
unsigned char x_165; 
lean::dec(x_162);
x_165 = 0;
return x_165;
}
else
{
unsigned char x_167; 
lean::dec(x_162);
x_167 = 1;
return x_167;
}
}
}
lbl_12:
{
obj* x_168; obj* x_169; obj* x_170; 
x_168 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_169 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
x_170 = lean::nat_dec_eq(x_168, x_169);
lean::dec(x_168);
if (lean::obj_tag(x_170) == 0)
{
unsigned char x_173; 
lean::dec(x_170);
x_173 = 0;
return x_173;
}
else
{
obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_170);
x_175 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_176 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_177 = lean::nat_dec_eq(x_175, x_176);
lean::dec(x_175);
if (lean::obj_tag(x_177) == 0)
{
unsigned char x_180; 
lean::dec(x_177);
x_180 = 0;
return x_180;
}
else
{
unsigned char x_182; 
lean::dec(x_177);
x_182 = 1;
return x_182;
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1() {
{
unsigned char x_0; obj* x_1; 
x_0 = 11;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2() {
{
unsigned char x_0; obj* x_1; 
x_0 = 5;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3() {
{
unsigned char x_0; obj* x_1; 
x_0 = 3;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4() {
{
unsigned char x_0; obj* x_1; 
x_0 = 7;
x_1 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; unsigned char x_4; unsigned char x_5; unsigned char x_6; obj* x_7; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types(x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
unsigned char _l_s4_lean_s2_ir_s27_valid__assign__binop__types(unsigned char x_0, unsigned char x_1, unsigned char x_2, unsigned char x_3) {
{
unsigned char x_4; unsigned char x_6; unsigned char x_8; unsigned char x_10; unsigned char x_12; unsigned char x_14; unsigned char x_16; 
switch (x_0) {
case 0:
{
unsigned char x_18; 
x_18 = 0;
x_4 = x_18;
goto lbl_5;
}
case 1:
{
unsigned char x_19; 
x_19 = 0;
x_4 = x_19;
goto lbl_5;
}
case 2:
{
unsigned char x_20; 
x_20 = 0;
x_4 = x_20;
goto lbl_5;
}
case 3:
{
unsigned char x_21; 
x_21 = 0;
x_4 = x_21;
goto lbl_5;
}
case 4:
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_23 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
unsigned char x_28; 
lean::dec(x_22);
lean::dec(x_24);
x_28 = 0;
return x_28;
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_24);
x_30 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_31 = lean::nat_dec_eq(x_22, x_30);
lean::dec(x_30);
lean::dec(x_22);
if (lean::obj_tag(x_31) == 0)
{
unsigned char x_35; 
lean::dec(x_31);
x_35 = 0;
return x_35;
}
else
{
unsigned char x_37; 
lean::dec(x_31);
x_37 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty(x_1);
return x_37;
}
}
}
case 5:
{
unsigned char x_38; 
x_38 = 0;
x_6 = x_38;
goto lbl_7;
}
case 6:
{
unsigned char x_39; 
x_39 = 0;
x_6 = x_39;
goto lbl_7;
}
case 7:
{
unsigned char x_40; 
x_40 = 0;
x_6 = x_40;
goto lbl_7;
}
case 8:
{
unsigned char x_41; 
x_41 = 0;
x_6 = x_41;
goto lbl_7;
}
case 9:
{
unsigned char x_42; 
x_42 = 0;
x_6 = x_42;
goto lbl_7;
}
case 10:
{
unsigned char x_43; 
x_43 = 0;
x_8 = x_43;
goto lbl_9;
}
case 11:
{
unsigned char x_44; 
x_44 = 0;
x_8 = x_44;
goto lbl_9;
}
case 12:
{
unsigned char x_45; 
x_45 = 0;
x_10 = x_45;
goto lbl_11;
}
case 13:
{
unsigned char x_46; 
x_46 = 0;
x_10 = x_46;
goto lbl_11;
}
case 14:
{
unsigned char x_47; 
x_47 = 0;
x_10 = x_47;
goto lbl_11;
}
case 15:
{
unsigned char x_48; 
x_48 = 0;
x_12 = x_48;
goto lbl_13;
}
case 16:
{
unsigned char x_49; 
x_49 = 0;
x_12 = x_49;
goto lbl_13;
}
case 17:
{
unsigned char x_50; 
x_50 = 0;
x_14 = x_50;
goto lbl_15;
}
case 18:
{
unsigned char x_51; 
x_51 = 0;
x_14 = x_51;
goto lbl_15;
}
case 19:
{
unsigned char x_52; 
x_52 = 0;
x_16 = x_52;
goto lbl_17;
}
case 20:
{
unsigned char x_53; 
x_53 = 0;
x_16 = x_53;
goto lbl_17;
}
case 21:
{
unsigned char x_54; 
x_54 = 0;
x_16 = x_54;
goto lbl_17;
}
case 22:
{
unsigned char x_55; 
x_55 = 0;
x_16 = x_55;
goto lbl_17;
}
case 23:
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_57 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_58 = lean::nat_dec_eq(x_56, x_57);
lean::dec(x_56);
if (lean::obj_tag(x_58) == 0)
{
unsigned char x_61; 
lean::dec(x_58);
x_61 = 0;
return x_61;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_58);
x_63 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_64 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2;
x_65 = lean::nat_dec_eq(x_63, x_64);
lean::dec(x_63);
if (lean::obj_tag(x_65) == 0)
{
unsigned char x_68; 
lean::dec(x_65);
x_68 = 0;
return x_68;
}
else
{
unsigned char x_70; 
lean::dec(x_65);
x_70 = 1;
return x_70;
}
}
}
case 24:
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_72 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_73 = lean::nat_dec_eq(x_71, x_72);
lean::dec(x_71);
if (lean::obj_tag(x_73) == 0)
{
unsigned char x_77; 
lean::dec(x_72);
lean::dec(x_73);
x_77 = 0;
return x_77;
}
else
{
obj* x_79; obj* x_80; 
lean::dec(x_73);
x_79 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_80 = lean::nat_dec_eq(x_79, x_72);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
unsigned char x_83; 
lean::dec(x_80);
x_83 = 0;
return x_83;
}
else
{
unsigned char x_85; 
lean::dec(x_80);
x_85 = 1;
return x_85;
}
}
}
case 25:
{
obj* x_86; obj* x_87; obj* x_88; 
x_86 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_87 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_88 = lean::nat_dec_eq(x_86, x_87);
lean::dec(x_86);
if (lean::obj_tag(x_88) == 0)
{
unsigned char x_92; 
lean::dec(x_88);
lean::dec(x_87);
x_92 = 0;
return x_92;
}
else
{
obj* x_94; obj* x_95; 
lean::dec(x_88);
x_94 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_95 = lean::nat_dec_eq(x_94, x_87);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
unsigned char x_98; 
lean::dec(x_95);
x_98 = 0;
return x_98;
}
else
{
obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_95);
x_100 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_101 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
x_102 = lean::nat_dec_eq(x_100, x_101);
lean::dec(x_100);
if (lean::obj_tag(x_102) == 0)
{
unsigned char x_105; 
lean::dec(x_102);
x_105 = 0;
return x_105;
}
else
{
unsigned char x_107; 
lean::dec(x_102);
x_107 = 1;
return x_107;
}
}
}
}
default:
{
obj* x_108; obj* x_109; obj* x_110; 
x_108 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_109 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_110 = lean::nat_dec_eq(x_108, x_109);
lean::dec(x_108);
if (lean::obj_tag(x_110) == 0)
{
unsigned char x_114; 
lean::dec(x_110);
lean::dec(x_109);
x_114 = 0;
return x_114;
}
else
{
obj* x_116; obj* x_117; 
lean::dec(x_110);
x_116 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_117 = lean::nat_dec_eq(x_116, x_109);
lean::dec(x_116);
if (lean::obj_tag(x_117) == 0)
{
unsigned char x_121; 
lean::dec(x_117);
lean::dec(x_109);
x_121 = 0;
return x_121;
}
else
{
obj* x_123; obj* x_124; 
lean::dec(x_117);
x_123 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_124 = lean::nat_dec_eq(x_123, x_109);
lean::dec(x_123);
if (lean::obj_tag(x_124) == 0)
{
unsigned char x_127; 
lean::dec(x_124);
x_127 = 0;
return x_127;
}
else
{
unsigned char x_129; 
lean::dec(x_124);
x_129 = 1;
return x_129;
}
}
}
}
}
lbl_5:
{
obj* x_130; obj* x_131; obj* x_132; 
x_130 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_131 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_132 = lean::nat_dec_eq(x_130, x_131);
lean::dec(x_131);
if (lean::obj_tag(x_132) == 0)
{
unsigned char x_136; 
lean::dec(x_132);
lean::dec(x_130);
x_136 = 0;
return x_136;
}
else
{
obj* x_138; obj* x_139; 
lean::dec(x_132);
x_138 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_139 = lean::nat_dec_eq(x_130, x_138);
lean::dec(x_138);
lean::dec(x_130);
if (lean::obj_tag(x_139) == 0)
{
unsigned char x_143; 
lean::dec(x_139);
x_143 = 0;
return x_143;
}
else
{
unsigned char x_145; 
lean::dec(x_139);
x_145 = _l_s4_lean_s2_ir_s13_is__arith__ty(x_1);
return x_145;
}
}
}
lbl_7:
{
obj* x_146; obj* x_147; obj* x_148; 
x_146 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_147 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_148 = lean::nat_dec_eq(x_146, x_147);
lean::dec(x_147);
if (lean::obj_tag(x_148) == 0)
{
unsigned char x_152; 
lean::dec(x_146);
lean::dec(x_148);
x_152 = 0;
return x_152;
}
else
{
obj* x_154; obj* x_155; 
lean::dec(x_148);
x_154 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_155 = lean::nat_dec_eq(x_146, x_154);
lean::dec(x_154);
if (lean::obj_tag(x_155) == 0)
{
unsigned char x_159; 
lean::dec(x_155);
lean::dec(x_146);
x_159 = 0;
return x_159;
}
else
{
obj* x_161; obj* x_162; 
lean::dec(x_155);
x_161 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_162 = lean::nat_dec_eq(x_146, x_161);
lean::dec(x_146);
if (lean::obj_tag(x_162) == 0)
{
unsigned char x_165; 
lean::dec(x_162);
x_165 = 0;
return x_165;
}
else
{
unsigned char x_167; 
lean::dec(x_162);
x_167 = 1;
return x_167;
}
}
}
}
lbl_9:
{
obj* x_168; obj* x_169; obj* x_170; 
x_168 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_169 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_170 = lean::nat_dec_eq(x_168, x_169);
lean::dec(x_169);
if (lean::obj_tag(x_170) == 0)
{
unsigned char x_174; 
lean::dec(x_170);
lean::dec(x_168);
x_174 = 0;
return x_174;
}
else
{
obj* x_176; obj* x_177; 
lean::dec(x_170);
x_176 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_177 = lean::nat_dec_eq(x_168, x_176);
lean::dec(x_176);
lean::dec(x_168);
if (lean::obj_tag(x_177) == 0)
{
unsigned char x_181; 
lean::dec(x_177);
x_181 = 0;
return x_181;
}
else
{
unsigned char x_183; 
lean::dec(x_177);
x_183 = _l_s4_lean_s2_ir_s16_is__bitshift__ty(x_1);
return x_183;
}
}
}
lbl_11:
{
obj* x_184; obj* x_185; obj* x_186; 
x_184 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_185 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_186 = lean::nat_dec_eq(x_184, x_185);
lean::dec(x_185);
if (lean::obj_tag(x_186) == 0)
{
unsigned char x_190; 
lean::dec(x_184);
lean::dec(x_186);
x_190 = 0;
return x_190;
}
else
{
obj* x_192; obj* x_193; 
lean::dec(x_186);
x_192 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_193 = lean::nat_dec_eq(x_184, x_192);
lean::dec(x_192);
lean::dec(x_184);
if (lean::obj_tag(x_193) == 0)
{
unsigned char x_197; 
lean::dec(x_193);
x_197 = 0;
return x_197;
}
else
{
unsigned char x_199; 
lean::dec(x_193);
x_199 = _l_s4_lean_s2_ir_s15_is__bitwise__ty(x_1);
return x_199;
}
}
}
lbl_13:
{
obj* x_200; obj* x_201; obj* x_202; 
x_200 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_201 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_202 = lean::nat_dec_eq(x_200, x_201);
lean::dec(x_200);
if (lean::obj_tag(x_202) == 0)
{
unsigned char x_205; 
lean::dec(x_202);
x_205 = 0;
return x_205;
}
else
{
obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_202);
x_207 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_208 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_209 = lean::nat_dec_eq(x_207, x_208);
lean::dec(x_208);
lean::dec(x_207);
if (lean::obj_tag(x_209) == 0)
{
unsigned char x_213; 
lean::dec(x_209);
x_213 = 0;
return x_213;
}
else
{
unsigned char x_215; 
lean::dec(x_209);
x_215 = _l_s4_lean_s2_ir_s13_is__arith__ty(x_2);
return x_215;
}
}
}
lbl_15:
{
obj* x_216; obj* x_217; obj* x_218; 
x_216 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_217 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_218 = lean::nat_dec_eq(x_216, x_217);
lean::dec(x_216);
if (lean::obj_tag(x_218) == 0)
{
unsigned char x_221; 
lean::dec(x_218);
x_221 = 0;
return x_221;
}
else
{
obj* x_223; obj* x_224; obj* x_225; 
lean::dec(x_218);
x_223 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_224 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_225 = lean::nat_dec_eq(x_223, x_224);
lean::dec(x_224);
lean::dec(x_223);
if (lean::obj_tag(x_225) == 0)
{
unsigned char x_229; 
lean::dec(x_225);
x_229 = 0;
return x_229;
}
else
{
unsigned char x_231; 
lean::dec(x_225);
x_231 = 1;
return x_231;
}
}
}
lbl_17:
{
obj* x_232; obj* x_233; obj* x_234; 
x_232 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_233 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_234 = lean::nat_dec_eq(x_232, x_233);
lean::dec(x_232);
if (lean::obj_tag(x_234) == 0)
{
unsigned char x_237; 
lean::dec(x_234);
x_237 = 0;
return x_237;
}
else
{
obj* x_239; obj* x_240; obj* x_241; 
lean::dec(x_234);
x_239 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_240 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_3);
x_241 = lean::nat_dec_eq(x_239, x_240);
lean::dec(x_240);
if (lean::obj_tag(x_241) == 0)
{
unsigned char x_245; 
lean::dec(x_241);
lean::dec(x_239);
x_245 = 0;
return x_245;
}
else
{
obj* x_247; obj* x_248; 
lean::dec(x_241);
x_247 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_248 = lean::nat_dec_eq(x_239, x_247);
lean::dec(x_239);
if (lean::obj_tag(x_248) == 0)
{
unsigned char x_251; 
lean::dec(x_248);
x_251 = 0;
return x_251;
}
else
{
unsigned char x_253; 
lean::dec(x_248);
x_253 = 1;
return x_253;
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s27_valid__assign__binop__types_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; unsigned char x_5; unsigned char x_6; unsigned char x_7; unsigned char x_8; obj* x_9; 
x_4 = lean::unbox(x_0);
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = lean::unbox(x_3);
x_8 = _l_s4_lean_s2_ir_s27_valid__assign__binop__types(x_4, x_5, x_6, x_7);
x_9 = lean::box(x_8);
return x_9;
}
}
obj* _init__l_s4_lean_s2_ir_s16_type__checker__m() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s16_type__checker__m_s3_run_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = _l_s4_lean_s2_ir_s11_mk__context;
lean::inc(x_4);
x_6 = lean::apply_2(x_0, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* _l_s4_lean_s2_ir_s16_type__checker__m_s3_run(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s16_type__checker__m_s3_run_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s11_match__type(obj* x_0, unsigned char x_1, unsigned char x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_6 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_7 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_2);
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; unsigned char x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_8);
x_12 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(x_0);
x_13 = 0;
x_14 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_13);
x_17 = x_16;
x_18 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__2;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_13);
x_21 = x_20;
x_22 = _l_s4_lean_s2_ir_s4_type_s10_to__format_s6___main(x_1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_13);
x_24 = x_23;
x_25 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__3;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_13);
x_28 = x_27;
x_29 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__4;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_13);
x_32 = x_31;
x_33 = _l_s4_lean_s2_ir_s4_type_s10_to__format_s6___main(x_2);
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_13);
x_35 = x_34;
lean::inc(x_25);
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_25);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_13);
x_38 = x_37;
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_4);
return x_40;
}
else
{
obj* x_43; obj* x_45; 
lean::dec(x_8);
lean::dec(x_0);
x_43 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_4);
return x_45;
}
}
}
obj* _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type mismatch, variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__2() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` has type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__3() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("`");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__4() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", but is expected to have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__5() {
{
unsigned char x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s11_match__type_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; unsigned char x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = _l_s4_lean_s2_ir_s11_match__type(x_0, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* _l_s4_lean_s2_ir_s9_get__type(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_1);
lean::inc(x_0);
lean::inc(x_2);
x_6 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_2, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; unsigned char x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_6);
x_8 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(x_0);
x_9 = 0;
x_10 = _l_s4_lean_s2_ir_s9_get__type_s11___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_9);
x_13 = x_12;
x_14 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__3;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_9);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
else
{
obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_2);
return x_25;
}
}
}
obj* _init__l_s4_lean_s2_ir_s9_get__type_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("undefined variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(obj* x_0, obj* x_1) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_9);
x_28 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_11, x_1);
return x_28;
}
}
else
{
obj* x_32; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_32 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_5, x_1);
return x_32;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_35);
lean::inc(x_1);
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_39);
lean::dec(x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
obj* x_56; 
lean::dec(x_37);
x_56 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_39, x_1);
return x_56;
}
}
else
{
obj* x_60; 
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_60 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_33, x_1);
return x_60;
}
}
}
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s9_set__type(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{
obj* x_6; 
lean::inc(x_0);
lean::inc(x_3);
x_6 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_3, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_6);
lean::dec(x_2);
x_9 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2(x_3, x_0, x_1);
x_10 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; unsigned char x_16; obj* x_18; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::unbox(x_13);
lean::dec(x_13);
x_18 = _l_s4_lean_s2_ir_s11_match__type(x_0, x_16, x_1, x_2, x_3);
return x_18;
}
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(obj* x_0, obj* x_1, unsigned char x_2) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; 
x_3 = lean::box(x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_0);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; unsigned char x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_14 = x_0;
}
lean::inc(x_8);
lean::inc(x_1);
x_17 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_8);
x_18 = lean::unbox(x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_22; unsigned char x_23; 
lean::inc(x_1);
lean::inc(x_8);
x_22 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_8, x_1);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_10);
lean::dec(x_8);
x_27 = lean::box(x_2);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_6);
lean::cnstr_set(x_28, 1, x_1);
lean::cnstr_set(x_28, 2, x_27);
lean::cnstr_set(x_28, 3, x_12);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_12, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_6, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_12);
return x_32;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_41 = x_0;
}
lean::inc(x_35);
lean::inc(x_1);
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::inc(x_1);
lean::inc(x_35);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_35);
lean::dec(x_37);
x_54 = lean::box(x_2);
if (lean::is_scalar(x_41)) {
 x_55 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_55 = x_41;
}
lean::cnstr_set(x_55, 0, x_33);
lean::cnstr_set(x_55, 1, x_1);
lean::cnstr_set(x_55, 2, x_54);
lean::cnstr_set(x_55, 3, x_39);
return x_55;
}
else
{
unsigned char x_57; 
lean::inc(x_39);
x_57 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_39);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_41);
x_59 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_39, x_1, x_2);
x_60 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_59, x_35, x_37, x_33);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_39, x_1, x_2);
if (lean::is_scalar(x_41)) {
 x_62 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_62 = x_41;
}
lean::cnstr_set(x_62, 0, x_33);
lean::cnstr_set(x_62, 1, x_35);
lean::cnstr_set(x_62, 2, x_37);
lean::cnstr_set(x_62, 3, x_61);
return x_62;
}
}
}
else
{
unsigned char x_64; 
lean::inc(x_33);
x_64 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_33);
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_41);
x_66 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_33, x_1, x_2);
x_67 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_66, x_35, x_37, x_39);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_33, x_1, x_2);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_35);
lean::cnstr_set(x_69, 2, x_37);
lean::cnstr_set(x_69, 3, x_39);
return x_69;
}
}
}
}
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2(obj* x_0, obj* x_1, unsigned char x_2) {
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__1(obj* x_0, obj* x_1, unsigned char x_2) {
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s2_ir_s9_set__type_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_lean_s2_ir_s9_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__3(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__2(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s9_set__type_s9___spec__1(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s11_check__type(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{
obj* x_6; 
lean::inc(x_0);
lean::inc(x_3);
x_6 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_3, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; unsigned char x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_2);
x_9 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(x_0);
x_10 = 0;
x_11 = _l_s4_lean_s2_ir_s11_check__type_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = _l_s4_lean_s2_ir_s11_check__type_s11___closed__2;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_10);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_3);
return x_20;
}
else
{
obj* x_21; unsigned char x_24; obj* x_26; 
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
x_24 = lean::unbox(x_21);
lean::dec(x_21);
x_26 = _l_s4_lean_s2_ir_s11_match__type(x_0, x_24, x_1, x_2, x_3);
return x_26;
}
}
}
obj* _init__l_s4_lean_s2_ir_s11_check__type_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type for variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s11_check__type_s11___closed__2() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` is not available");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s11_check__type_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_lean_s2_ir_s11_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s15_check__ne__type(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{
obj* x_7; 
lean::dec(x_2);
lean::inc(x_0);
lean::inc(x_3);
x_7 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_3, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; unsigned char x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_9 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(x_0);
x_10 = 0;
x_11 = _l_s4_lean_s2_ir_s11_check__type_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = _l_s4_lean_s2_ir_s11_check__type_s11___closed__2;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_10);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_3);
return x_20;
}
else
{
obj* x_21; unsigned char x_24; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_7, 0);
lean::inc(x_21);
lean::dec(x_7);
x_24 = lean::unbox(x_21);
lean::dec(x_21);
x_26 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_24);
x_27 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_28 = lean::nat_dec_eq(x_26, x_27);
lean::dec(x_27);
lean::dec(x_26);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_35; 
lean::dec(x_0);
lean::dec(x_28);
x_33 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_3);
return x_35;
}
else
{
obj* x_37; unsigned char x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_28);
x_37 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__1(x_0);
x_38 = 0;
x_39 = _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__1;
lean::inc(x_39);
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_37);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_38);
x_42 = x_41;
x_43 = _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__2;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_38);
x_46 = x_45;
x_47 = _l_s4_lean_s2_ir_s4_type_s10_to__format_s6___main(x_1);
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_38);
x_49 = x_48;
x_50 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__3;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_49);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_38);
x_53 = x_52;
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_3);
return x_55;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__2() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` must not have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s15_check__ne__type_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_lean_s2_ir_s15_check__ne__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; 
x_1 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* _init__l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid literal");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s16_invalid__literal(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s7_literal_s5_check(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{

lean::dec(x_2);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_6 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_7 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; 
lean::dec(x_8);
x_11 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
else
{
obj* x_15; obj* x_17; 
lean::dec(x_8);
x_15 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
}
case 1:
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_19 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_20 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_21 = lean::nat_dec_eq(x_19, x_20);
lean::dec(x_19);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_26; 
lean::dec(x_21);
x_24 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_3);
return x_26;
}
else
{
obj* x_28; obj* x_30; 
lean::dec(x_21);
x_28 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_3);
return x_30;
}
}
case 2:
{
obj* x_31; unsigned char x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty(x_1);
x_35 = _l_s3_int_s4_zero;
x_36 = lean::int_dec_lt(x_31, x_35);
lean::dec(x_31);
if (x_34 == 0)
{
obj* x_38; 
x_38 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_36);
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
lean::inc(x_38);
if (lean::is_shared(x_38)) {
 lean::dec(x_38);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_38, 0);
 x_43 = x_38;
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_3);
return x_45;
}
else
{

if (lean::obj_tag(x_36) == 0)
{
obj* x_48; obj* x_50; 
lean::dec(x_36);
lean::dec(x_38);
x_48 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_3);
return x_50;
}
else
{
unsigned char x_52; 
lean::dec(x_36);
x_52 = _l_s4_lean_s2_ir_s21_is__signed__arith__ty(x_1);
if (x_52 == 0)
{
obj* x_54; 
lean::inc(x_38);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_38);
lean::cnstr_set(x_54, 1, x_3);
return x_54;
}
else
{
obj* x_56; obj* x_58; 
lean::dec(x_38);
x_56 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_3);
return x_58;
}
}
}
}
else
{

if (lean::obj_tag(x_36) == 0)
{
obj* x_60; obj* x_62; 
lean::dec(x_36);
x_60 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_3);
return x_62;
}
else
{
unsigned char x_64; 
lean::dec(x_36);
x_64 = _l_s4_lean_s2_ir_s21_is__signed__arith__ty(x_1);
if (x_64 == 0)
{
obj* x_65; obj* x_67; 
x_65 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_3);
return x_67;
}
else
{
obj* x_68; obj* x_70; 
x_68 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_3);
return x_70;
}
}
}
}
default:
{
obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_0);
x_72 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1);
x_73 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2;
x_74 = lean::nat_dec_eq(x_72, x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_77; 
lean::dec(x_74);
x_76 = _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1;
x_77 = lean::nat_dec_eq(x_72, x_76);
lean::dec(x_72);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_82; 
lean::dec(x_77);
x_80 = _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1;
lean::inc(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_3);
return x_82;
}
else
{
obj* x_84; obj* x_86; 
lean::dec(x_77);
x_84 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_3);
return x_86;
}
}
else
{
obj* x_89; obj* x_91; 
lean::dec(x_72);
lean::dec(x_74);
x_89 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_3);
return x_91;
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s7_literal_s5_check_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_lean_s2_ir_s7_literal_s5_check(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s9_get__decl(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_5 = x_1;
}
lean::inc(x_0);
x_7 = lean::apply_1(x_3, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; unsigned char x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_9 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(x_0);
x_10 = 0;
x_11 = _l_s4_lean_s2_ir_s9_get__decl_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__3;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_10);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
if (lean::is_scalar(x_5)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_5;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
}
else
{
obj* x_22; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_7, 0);
lean::inc(x_22);
lean::dec(x_7);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_5)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_5;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_2);
return x_26;
}
}
}
obj* _init__l_s4_lean_s2_ir_s9_get__decl_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown function `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s18_set__result__types_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = _l_s4_lean_s2_ir_s9_set__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s18_set__result__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = _l_s4_lean_s2_ir_s9_set__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s5_instr_s12_infer__types(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; unsigned char x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_8 = _l_s4_lean_s2_ir_s9_set__type(x_5, x_7, x_1, x_2);
x_3 = x_8;
goto lbl_4;
}
case 1:
{
obj* x_9; unsigned char x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_12 = _l_s4_lean_s2_ir_s9_set__type(x_9, x_11, x_1, x_2);
x_3 = x_12;
goto lbl_4;
}
case 2:
{
obj* x_13; unsigned char x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_16 = _l_s4_lean_s2_ir_s9_set__type(x_13, x_15, x_1, x_2);
x_3 = x_16;
goto lbl_4;
}
case 3:
{
obj* x_17; unsigned char x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_20 = _l_s4_lean_s2_ir_s9_set__type(x_17, x_19, x_1, x_2);
x_3 = x_20;
goto lbl_4;
}
case 4:
{
obj* x_22; obj* x_24; 
lean::dec(x_1);
x_22 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_2);
x_3 = x_24;
goto lbl_4;
}
case 5:
{
obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_33; obj* x_35; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
lean::inc(x_1);
x_30 = _l_s4_lean_s2_ir_s9_get__decl(x_27, x_1, x_2);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_35 = x_30;
}
if (lean::obj_tag(x_31) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_1);
lean::dec(x_25);
x_38 = lean::cnstr_get(x_31, 0);
lean::inc(x_38);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_40 = x_31;
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_33);
x_3 = x_42;
goto lbl_4;
}
else
{
obj* x_44; obj* x_47; obj* x_48; unsigned char x_51; obj* x_53; 
lean::dec(x_35);
x_44 = lean::cnstr_get(x_31, 0);
lean::inc(x_44);
lean::dec(x_31);
x_47 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_44);
x_48 = lean::cnstr_get(x_47, 2);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::unbox(x_48);
lean::dec(x_48);
x_53 = _l_s4_lean_s2_ir_s9_set__type(x_25, x_51, x_1, x_33);
x_3 = x_53;
goto lbl_4;
}
}
case 6:
{
obj* x_54; unsigned char x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
x_56 = 11;
x_57 = _l_s4_lean_s2_ir_s9_set__type(x_54, x_56, x_1, x_2);
x_3 = x_57;
goto lbl_4;
}
case 7:
{
obj* x_59; obj* x_61; 
lean::dec(x_1);
x_59 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_2);
x_3 = x_61;
goto lbl_4;
}
case 8:
{
obj* x_62; unsigned char x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_0, 0);
lean::inc(x_62);
x_64 = 11;
x_65 = _l_s4_lean_s2_ir_s9_set__type(x_62, x_64, x_1, x_2);
x_3 = x_65;
goto lbl_4;
}
case 9:
{
obj* x_67; obj* x_69; 
lean::dec(x_1);
x_67 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_2);
x_3 = x_69;
goto lbl_4;
}
case 10:
{
obj* x_70; unsigned char x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_0, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_73 = _l_s4_lean_s2_ir_s9_set__type(x_70, x_72, x_1, x_2);
x_3 = x_73;
goto lbl_4;
}
case 11:
{
obj* x_74; unsigned char x_76; obj* x_77; 
x_74 = lean::cnstr_get(x_0, 0);
lean::inc(x_74);
x_76 = 11;
x_77 = _l_s4_lean_s2_ir_s9_set__type(x_74, x_76, x_1, x_2);
x_3 = x_77;
goto lbl_4;
}
case 12:
{
obj* x_78; unsigned char x_80; obj* x_81; 
x_78 = lean::cnstr_get(x_0, 0);
lean::inc(x_78);
x_80 = 11;
x_81 = _l_s4_lean_s2_ir_s9_set__type(x_78, x_80, x_1, x_2);
x_3 = x_81;
goto lbl_4;
}
case 13:
{
obj* x_82; unsigned char x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_0, 0);
lean::inc(x_82);
x_84 = 11;
x_85 = _l_s4_lean_s2_ir_s9_set__type(x_82, x_84, x_1, x_2);
x_3 = x_85;
goto lbl_4;
}
case 14:
{
obj* x_86; unsigned char x_88; obj* x_89; 
x_86 = lean::cnstr_get(x_0, 0);
lean::inc(x_86);
x_88 = 11;
x_89 = _l_s4_lean_s2_ir_s9_set__type(x_86, x_88, x_1, x_2);
x_3 = x_89;
goto lbl_4;
}
default:
{
obj* x_91; obj* x_93; 
lean::dec(x_1);
x_91 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_2);
x_3 = x_93;
goto lbl_4;
}
}
lbl_4:
{
obj* x_94; obj* x_96; obj* x_98; 
x_94 = lean::cnstr_get(x_3, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_3, 1);
lean::inc(x_96);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_98 = x_3;
}
if (lean::obj_tag(x_94) == 0)
{
obj* x_99; obj* x_101; obj* x_102; unsigned char x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_99 = lean::cnstr_get(x_94, 0);
lean::inc(x_99);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_101 = x_94;
}
x_102 = _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(x_0);
x_103 = 0;
x_104 = _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_104);
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_102);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_103);
x_107 = x_106;
x_108 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_108);
x_110 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
lean::cnstr_set_scalar(x_110, sizeof(void*)*2, x_103);
x_111 = x_110;
x_112 = lean::alloc_cnstr(1, 0, 0);
;
x_113 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set(x_113, 1, x_112);
lean::cnstr_set_scalar(x_113, sizeof(void*)*2, x_103);
x_114 = x_113;
x_115 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_99);
lean::cnstr_set_scalar(x_115, sizeof(void*)*2, x_103);
x_116 = x_115;
if (lean::is_scalar(x_101)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_101;
}
lean::cnstr_set(x_117, 0, x_116);
if (lean::is_scalar(x_98)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_98;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_96);
return x_118;
}
else
{
obj* x_120; 
lean::dec(x_0);
if (lean::is_scalar(x_98)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_98;
}
lean::cnstr_set(x_120, 0, x_94);
lean::cnstr_set(x_120, 1, x_96);
return x_120;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_phi_s12_infer__types(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; unsigned char x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_6 = _l_s4_lean_s2_ir_s9_set__type(x_3, x_5, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_15; unsigned char x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
}
x_15 = _l_s4_lean_s2_ir_s3_phi_s10_to__format_s6___main(x_0);
x_16 = 0;
x_17 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_16);
x_20 = x_19;
x_21 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_16);
x_24 = x_23;
x_25 = lean::alloc_cnstr(1, 0, 0);
;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_16);
x_27 = x_26;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_16);
x_29 = x_28;
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_29);
if (lean::is_scalar(x_11)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_11;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_9);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_0);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
obj* _l_s4_lean_s2_ir_s3_arg_s12_infer__types(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; unsigned char x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*1);
lean::dec(x_0);
x_7 = _l_s4_lean_s2_ir_s9_set__type(x_3, x_5, x_1, x_2);
return x_7;
}
}
obj* _l_s4_lean_s2_ir_s5_block_s12_infer__types(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
x_6 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; unsigned char x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
}
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main_s9___spec__4(x_16);
x_20 = 0;
x_21 = _l_s4_lean_s2_ir_s5_block_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_20);
x_24 = x_23;
x_25 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_20);
x_28 = x_27;
x_29 = lean::alloc_cnstr(1, 0, 0);
;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_20);
x_31 = x_30;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_13);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_20);
x_33 = x_32;
if (lean::is_scalar(x_15)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_15;
}
lean::cnstr_set(x_34, 0, x_33);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_36 = x_7;
}
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__2(x_37, x_1, x_9);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_45; obj* x_48; obj* x_51; unsigned char x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
lean::dec(x_0);
x_51 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main_s9___spec__4(x_48);
x_52 = 0;
x_53 = _l_s4_lean_s2_ir_s5_block_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_52);
x_56 = x_55;
x_57 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_52);
x_60 = x_59;
x_61 = lean::alloc_cnstr(1, 0, 0);
;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_52);
x_63 = x_62;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_45);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_52);
x_65 = x_64;
if (lean::is_scalar(x_36)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_36;
}
lean::cnstr_set(x_66, 0, x_65);
if (lean::is_scalar(x_11)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_11;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_42);
return x_67;
}
else
{
obj* x_70; 
lean::dec(x_36);
lean::dec(x_0);
if (lean::is_scalar(x_11)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_11;
}
lean::cnstr_set(x_70, 0, x_40);
lean::cnstr_set(x_70, 1, x_42);
return x_70;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_phi_s12_infer__types(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s5_instr_s12_infer__types(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s12_infer__types_s9___spec__2(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::inc(x_1);
x_16 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__1(x_13, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_30; unsigned char x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_26 = x_17;
}
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
lean::dec(x_8);
x_30 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(x_27);
x_31 = 0;
x_32 = _l_s4_lean_s2_ir_s6_header_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_31);
x_35 = x_34;
x_36 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_36);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_31);
x_39 = x_38;
x_40 = lean::alloc_cnstr(1, 0, 0);
;
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_31);
x_42 = x_41;
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_24);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_31);
x_44 = x_43;
if (lean::is_scalar(x_26)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_26;
}
lean::cnstr_set(x_45, 0, x_44);
if (lean::is_scalar(x_21)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_21;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_19);
return x_46;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_51; 
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_47 = x_17;
}
x_48 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__2(x_10, x_1, x_19);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_54; obj* x_57; obj* x_60; unsigned char x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_54 = lean::cnstr_get(x_49, 0);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::cnstr_get(x_8, 0);
lean::inc(x_57);
lean::dec(x_8);
x_60 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(x_57);
x_61 = 0;
x_62 = _l_s4_lean_s2_ir_s6_header_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_61);
x_65 = x_64;
x_66 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_66);
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_66);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_61);
x_69 = x_68;
x_70 = lean::alloc_cnstr(1, 0, 0);
;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_61);
x_72 = x_71;
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_54);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_61);
x_74 = x_73;
if (lean::is_scalar(x_47)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_47;
}
lean::cnstr_set(x_75, 0, x_74);
if (lean::is_scalar(x_21)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_21;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_51);
return x_76;
}
else
{
obj* x_80; obj* x_81; 
lean::dec(x_49);
lean::dec(x_8);
lean::inc(x_51);
if (lean::is_scalar(x_47)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_47;
}
lean::cnstr_set(x_80, 0, x_51);
if (lean::is_scalar(x_21)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_21;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_51);
return x_81;
}
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_arg_s12_infer__types(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s5_block_s12_infer__types(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main_s9___spec__2(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s12_infer__types(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s4_decl_s12_infer__types_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s2_ir_s12_infer__types(obj* x_0, obj* x_1) {
{
obj* x_3; obj* x_4; obj* x_5; obj* x_8; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s4_decl_s12_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_5 = lean::cnstr_get(x_4, 2);
lean::inc(x_5);
lean::dec(x_4);
x_8 = _l_s4_lean_s2_ir_s16_type__checker__m_s3_run_s6___rarg(x_3, x_1, x_5);
return x_8;
}
}
obj* _l_s4_lean_s2_ir_s17_check__arg__types_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_0) == 0)
{

lean::dec(x_0);
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
x_7 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_11; obj* x_13; 
lean::dec(x_1);
x_11 = _l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_25; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_2);
x_23 = _l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_3);
return x_25;
}
else
{
obj* x_26; obj* x_28; unsigned char x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_1, 1);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::cnstr_get_scalar<unsigned char>(x_26, sizeof(void*)*1);
lean::dec(x_26);
lean::inc(x_2);
x_34 = _l_s4_lean_s2_ir_s11_check__type(x_14, x_31, x_2, x_3);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_39 = x_34;
}
if (lean::obj_tag(x_35) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_16);
lean::dec(x_2);
lean::dec(x_28);
x_43 = lean::cnstr_get(x_35, 0);
lean::inc(x_43);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_45 = x_35;
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_37);
return x_47;
}
else
{
obj* x_50; 
lean::dec(x_39);
lean::dec(x_35);
x_50 = _l_s4_lean_s2_ir_s17_check__arg__types_s6___main(x_16, x_28, x_2, x_37);
return x_50;
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("unexpected number of arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s17_check__arg__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s2_ir_s17_check__arg__types_s6___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s5_instr_s5_check(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
unsigned char x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = _l_s4_lean_s2_ir_s9_get__type(x_6, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_16 = x_9;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
x_3 = x_18;
goto lbl_4;
}
else
{
obj* x_19; obj* x_22; unsigned char x_23; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
x_22 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_5);
x_23 = lean::unbox(x_19);
lean::dec(x_19);
x_25 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_23);
x_26 = lean::nat_dec_eq(x_22, x_25);
lean::dec(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; obj* x_32; 
lean::dec(x_26);
x_30 = _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__1;
lean::inc(x_30);
if (lean::is_scalar(x_13)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_13;
}
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_11);
x_3 = x_32;
goto lbl_4;
}
else
{
obj* x_34; obj* x_36; 
lean::dec(x_26);
x_34 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_34);
if (lean::is_scalar(x_13)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_13;
}
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_11);
x_3 = x_36;
goto lbl_4;
}
}
}
case 1:
{
unsigned char x_37; obj* x_38; obj* x_40; 
x_37 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_38 = lean::cnstr_get(x_0, 1);
lean::inc(x_38);
x_40 = _l_s4_lean_s2_ir_s7_literal_s5_check(x_38, x_37, x_1, x_2);
x_3 = x_40;
goto lbl_4;
}
case 2:
{
unsigned char x_41; unsigned char x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; 
x_41 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_42 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2 + 1);
x_43 = lean::cnstr_get(x_0, 1);
lean::inc(x_43);
x_45 = _l_s4_lean_s2_ir_s9_get__type(x_43, x_1, x_2);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_50 = x_45;
}
if (lean::obj_tag(x_46) == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_46, 0);
lean::inc(x_51);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_53 = x_46;
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_50)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_50;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
x_3 = x_55;
goto lbl_4;
}
else
{
obj* x_56; unsigned char x_59; unsigned char x_61; 
x_56 = lean::cnstr_get(x_46, 0);
lean::inc(x_56);
lean::dec(x_46);
x_59 = lean::unbox(x_56);
lean::dec(x_56);
x_61 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types(x_42, x_41, x_59);
if (x_61 == 0)
{
obj* x_62; obj* x_64; 
x_62 = _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__2;
lean::inc(x_62);
if (lean::is_scalar(x_50)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_50;
}
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_48);
x_3 = x_64;
goto lbl_4;
}
else
{
obj* x_65; obj* x_67; 
x_65 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_65);
if (lean::is_scalar(x_50)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_50;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_48);
x_3 = x_67;
goto lbl_4;
}
}
}
case 3:
{
unsigned char x_68; unsigned char x_69; obj* x_70; obj* x_72; obj* x_75; obj* x_76; obj* x_78; obj* x_80; 
x_68 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_69 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3 + 1);
x_70 = lean::cnstr_get(x_0, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_0, 2);
lean::inc(x_72);
lean::inc(x_1);
x_75 = _l_s4_lean_s2_ir_s9_get__type(x_70, x_1, x_2);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 x_80 = x_75;
}
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_72);
lean::dec(x_1);
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_85 = x_76;
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_80)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_80;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_78);
x_3 = x_87;
goto lbl_4;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_94; 
x_88 = lean::cnstr_get(x_76, 0);
lean::inc(x_88);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_90 = x_76;
}
x_91 = _l_s4_lean_s2_ir_s9_get__type(x_72, x_1, x_78);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_88);
x_98 = lean::cnstr_get(x_92, 0);
lean::inc(x_98);
lean::dec(x_92);
if (lean::is_scalar(x_90)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_90;
}
lean::cnstr_set(x_101, 0, x_98);
if (lean::is_scalar(x_80)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_80;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_94);
x_3 = x_102;
goto lbl_4;
}
else
{
obj* x_104; unsigned char x_107; unsigned char x_109; unsigned char x_111; 
lean::dec(x_90);
x_104 = lean::cnstr_get(x_92, 0);
lean::inc(x_104);
lean::dec(x_92);
x_107 = lean::unbox(x_88);
lean::dec(x_88);
x_109 = lean::unbox(x_104);
lean::dec(x_104);
x_111 = _l_s4_lean_s2_ir_s27_valid__assign__binop__types(x_69, x_68, x_107, x_109);
if (x_111 == 0)
{
obj* x_112; obj* x_114; 
x_112 = _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__3;
lean::inc(x_112);
if (lean::is_scalar(x_80)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_80;
}
lean::cnstr_set(x_114, 0, x_112);
lean::cnstr_set(x_114, 1, x_94);
x_3 = x_114;
goto lbl_4;
}
else
{
obj* x_115; obj* x_117; 
x_115 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_115);
if (lean::is_scalar(x_80)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_80;
}
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_94);
x_3 = x_117;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_118; unsigned char x_120; obj* x_121; 
x_118 = lean::cnstr_get(x_0, 0);
lean::inc(x_118);
x_120 = 11;
x_121 = _l_s4_lean_s2_ir_s11_check__type(x_118, x_120, x_1, x_2);
x_3 = x_121;
goto lbl_4;
}
case 5:
{
obj* x_122; obj* x_124; obj* x_127; obj* x_128; obj* x_130; obj* x_132; 
x_122 = lean::cnstr_get(x_0, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_0, 2);
lean::inc(x_124);
lean::inc(x_1);
x_127 = _l_s4_lean_s2_ir_s9_get__decl(x_122, x_1, x_2);
x_128 = lean::cnstr_get(x_127, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_127, 1);
lean::inc(x_130);
if (lean::is_shared(x_127)) {
 lean::dec(x_127);
 x_132 = lean::box(0);
} else {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_132 = x_127;
}
if (lean::obj_tag(x_128) == 0)
{
obj* x_135; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_124);
lean::dec(x_1);
x_135 = lean::cnstr_get(x_128, 0);
lean::inc(x_135);
if (lean::is_shared(x_128)) {
 lean::dec(x_128);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_128, 0);
 x_137 = x_128;
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_135);
if (lean::is_scalar(x_132)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_132;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_130);
x_3 = x_139;
goto lbl_4;
}
else
{
obj* x_141; obj* x_144; obj* x_145; obj* x_148; 
lean::dec(x_132);
x_141 = lean::cnstr_get(x_128, 0);
lean::inc(x_141);
lean::dec(x_128);
x_144 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_141);
x_145 = lean::cnstr_get(x_144, 1);
lean::inc(x_145);
lean::dec(x_144);
x_148 = _l_s4_lean_s2_ir_s17_check__arg__types_s6___main(x_124, x_145, x_1, x_130);
x_3 = x_148;
goto lbl_4;
}
}
case 6:
{
obj* x_150; obj* x_152; 
lean::dec(x_1);
x_150 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_150);
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_150);
lean::cnstr_set(x_152, 1, x_2);
x_3 = x_152;
goto lbl_4;
}
case 7:
{
obj* x_153; obj* x_155; unsigned char x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_164; 
x_153 = lean::cnstr_get(x_0, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_0, 1);
lean::inc(x_155);
x_157 = 11;
lean::inc(x_1);
x_159 = _l_s4_lean_s2_ir_s11_check__type(x_153, x_157, x_1, x_2);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
if (lean::is_shared(x_159)) {
 lean::dec(x_159);
 x_164 = lean::box(0);
} else {
 lean::cnstr_release(x_159, 0);
 lean::cnstr_release(x_159, 1);
 x_164 = x_159;
}
if (lean::obj_tag(x_160) == 0)
{
obj* x_167; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_155);
lean::dec(x_1);
x_167 = lean::cnstr_get(x_160, 0);
lean::inc(x_167);
if (lean::is_shared(x_160)) {
 lean::dec(x_160);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_160, 0);
 x_169 = x_160;
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
if (lean::is_scalar(x_164)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_164;
}
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_162);
x_3 = x_171;
goto lbl_4;
}
else
{
obj* x_174; 
lean::dec(x_160);
lean::dec(x_164);
x_174 = _l_s4_lean_s2_ir_s11_check__type(x_155, x_157, x_1, x_162);
x_3 = x_174;
goto lbl_4;
}
}
case 8:
{
obj* x_175; unsigned char x_177; obj* x_178; 
x_175 = lean::cnstr_get(x_0, 1);
lean::inc(x_175);
x_177 = 11;
x_178 = _l_s4_lean_s2_ir_s11_check__type(x_175, x_177, x_1, x_2);
x_3 = x_178;
goto lbl_4;
}
case 9:
{
obj* x_179; obj* x_181; unsigned char x_183; obj* x_185; obj* x_186; obj* x_188; obj* x_190; 
x_179 = lean::cnstr_get(x_0, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_0, 1);
lean::inc(x_181);
x_183 = 11;
lean::inc(x_1);
x_185 = _l_s4_lean_s2_ir_s11_check__type(x_179, x_183, x_1, x_2);
x_186 = lean::cnstr_get(x_185, 0);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_185, 1);
lean::inc(x_188);
if (lean::is_shared(x_185)) {
 lean::dec(x_185);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_190 = x_185;
}
if (lean::obj_tag(x_186) == 0)
{
obj* x_193; obj* x_195; obj* x_196; obj* x_197; 
lean::dec(x_181);
lean::dec(x_1);
x_193 = lean::cnstr_get(x_186, 0);
lean::inc(x_193);
if (lean::is_shared(x_186)) {
 lean::dec(x_186);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_186, 0);
 x_195 = x_186;
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
if (lean::is_scalar(x_190)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_190;
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_188);
x_3 = x_197;
goto lbl_4;
}
else
{
obj* x_200; 
lean::dec(x_190);
lean::dec(x_186);
x_200 = _l_s4_lean_s2_ir_s15_check__ne__type(x_181, x_183, x_1, x_188);
x_3 = x_200;
goto lbl_4;
}
}
case 10:
{
obj* x_201; obj* x_203; unsigned char x_205; obj* x_207; obj* x_208; obj* x_210; obj* x_212; 
x_201 = lean::cnstr_get(x_0, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_0, 1);
lean::inc(x_203);
x_205 = 11;
lean::inc(x_1);
x_207 = _l_s4_lean_s2_ir_s11_check__type(x_203, x_205, x_1, x_2);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_212 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 lean::cnstr_release(x_207, 1);
 x_212 = x_207;
}
if (lean::obj_tag(x_208) == 0)
{
obj* x_215; obj* x_217; obj* x_218; obj* x_219; 
lean::dec(x_201);
lean::dec(x_1);
x_215 = lean::cnstr_get(x_208, 0);
lean::inc(x_215);
if (lean::is_shared(x_208)) {
 lean::dec(x_208);
 x_217 = lean::box(0);
} else {
 lean::cnstr_release(x_208, 0);
 x_217 = x_208;
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_215);
if (lean::is_scalar(x_212)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_212;
}
lean::cnstr_set(x_219, 0, x_218);
lean::cnstr_set(x_219, 1, x_210);
x_3 = x_219;
goto lbl_4;
}
else
{
obj* x_222; 
lean::dec(x_208);
lean::dec(x_212);
x_222 = _l_s4_lean_s2_ir_s15_check__ne__type(x_201, x_205, x_1, x_210);
x_3 = x_222;
goto lbl_4;
}
}
case 11:
{
obj* x_223; obj* x_225; obj* x_229; obj* x_230; obj* x_232; obj* x_234; 
x_223 = lean::cnstr_get(x_0, 1);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_0, 2);
lean::inc(x_225);
lean::inc(x_1);
lean::inc(x_225);
x_229 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__1(x_225, x_1, x_2);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_229, 1);
lean::inc(x_232);
if (lean::is_shared(x_229)) {
 lean::dec(x_229);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_229, 0);
 lean::cnstr_release(x_229, 1);
 x_234 = x_229;
}
if (lean::obj_tag(x_230) == 0)
{
obj* x_238; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_225);
lean::dec(x_223);
lean::dec(x_1);
x_238 = lean::cnstr_get(x_230, 0);
lean::inc(x_238);
if (lean::is_shared(x_230)) {
 lean::dec(x_230);
 x_240 = lean::box(0);
} else {
 lean::cnstr_release(x_230, 0);
 x_240 = x_230;
}
if (lean::is_scalar(x_240)) {
 x_241 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_241 = x_240;
}
lean::cnstr_set(x_241, 0, x_238);
if (lean::is_scalar(x_234)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_234;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_232);
x_3 = x_242;
goto lbl_4;
}
else
{
obj* x_243; obj* x_245; obj* x_246; obj* x_248; 
if (lean::is_shared(x_230)) {
 lean::dec(x_230);
 x_243 = lean::box(0);
} else {
 lean::cnstr_release(x_230, 0);
 x_243 = x_230;
}
lean::inc(x_1);
x_245 = _l_s4_lean_s2_ir_s9_get__decl(x_223, x_1, x_232);
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 1);
lean::inc(x_248);
lean::dec(x_245);
if (lean::obj_tag(x_246) == 0)
{
obj* x_253; obj* x_256; obj* x_257; 
lean::dec(x_225);
lean::dec(x_1);
x_253 = lean::cnstr_get(x_246, 0);
lean::inc(x_253);
lean::dec(x_246);
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_253);
if (lean::is_scalar(x_234)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_234;
}
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_248);
x_3 = x_257;
goto lbl_4;
}
else
{
obj* x_259; obj* x_262; obj* x_263; obj* x_264; obj* x_268; obj* x_269; 
lean::dec(x_243);
x_259 = lean::cnstr_get(x_246, 0);
lean::inc(x_259);
lean::dec(x_246);
x_262 = _l_s4_list_s6_length_s6___main_s6___rarg(x_225);
x_263 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_259);
x_264 = lean::cnstr_get(x_263, 1);
lean::inc(x_264);
lean::dec(x_263);
lean::inc(x_264);
x_268 = _l_s4_list_s6_length_s6___main_s6___rarg(x_264);
x_269 = lean::nat_dec_le(x_262, x_268);
lean::dec(x_268);
lean::dec(x_262);
if (lean::obj_tag(x_269) == 0)
{
obj* x_275; obj* x_277; 
lean::dec(x_1);
lean::dec(x_269);
lean::dec(x_264);
x_275 = _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__4;
lean::inc(x_275);
if (lean::is_scalar(x_234)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_234;
}
lean::cnstr_set(x_277, 0, x_275);
lean::cnstr_set(x_277, 1, x_248);
x_3 = x_277;
goto lbl_4;
}
else
{
obj* x_280; 
lean::dec(x_234);
lean::dec(x_269);
x_280 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2(x_264, x_1, x_248);
x_3 = x_280;
goto lbl_4;
}
}
}
}
case 12:
{
obj* x_281; obj* x_283; 
x_281 = lean::cnstr_get(x_0, 1);
lean::inc(x_281);
x_283 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__3(x_281, x_1, x_2);
x_3 = x_283;
goto lbl_4;
}
case 13:
{
obj* x_284; obj* x_286; unsigned char x_288; obj* x_290; obj* x_291; obj* x_293; obj* x_295; 
x_284 = lean::cnstr_get(x_0, 1);
lean::inc(x_284);
x_286 = lean::cnstr_get(x_0, 2);
lean::inc(x_286);
x_288 = 5;
lean::inc(x_1);
x_290 = _l_s4_lean_s2_ir_s11_check__type(x_284, x_288, x_1, x_2);
x_291 = lean::cnstr_get(x_290, 0);
lean::inc(x_291);
x_293 = lean::cnstr_get(x_290, 1);
lean::inc(x_293);
if (lean::is_shared(x_290)) {
 lean::dec(x_290);
 x_295 = lean::box(0);
} else {
 lean::cnstr_release(x_290, 0);
 lean::cnstr_release(x_290, 1);
 x_295 = x_290;
}
if (lean::obj_tag(x_291) == 0)
{
obj* x_298; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_1);
lean::dec(x_286);
x_298 = lean::cnstr_get(x_291, 0);
lean::inc(x_298);
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_300 = x_291;
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
if (lean::is_scalar(x_295)) {
 x_302 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_302 = x_295;
}
lean::cnstr_set(x_302, 0, x_301);
lean::cnstr_set(x_302, 1, x_293);
x_3 = x_302;
goto lbl_4;
}
else
{
obj* x_305; 
lean::dec(x_295);
lean::dec(x_291);
x_305 = _l_s4_lean_s2_ir_s11_check__type(x_286, x_288, x_1, x_293);
x_3 = x_305;
goto lbl_4;
}
}
case 14:
{
unsigned char x_306; obj* x_307; obj* x_309; obj* x_311; obj* x_312; obj* x_313; 
x_306 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_307 = lean::cnstr_get(x_0, 1);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_0, 2);
lean::inc(x_309);
x_311 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_306);
x_312 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_313 = lean::nat_dec_eq(x_311, x_312);
lean::dec(x_311);
if (lean::obj_tag(x_313) == 0)
{
unsigned char x_316; obj* x_318; obj* x_319; obj* x_321; obj* x_323; 
lean::dec(x_313);
x_316 = 5;
lean::inc(x_1);
x_318 = _l_s4_lean_s2_ir_s11_check__type(x_307, x_316, x_1, x_2);
x_319 = lean::cnstr_get(x_318, 0);
lean::inc(x_319);
x_321 = lean::cnstr_get(x_318, 1);
lean::inc(x_321);
if (lean::is_shared(x_318)) {
 lean::dec(x_318);
 x_323 = lean::box(0);
} else {
 lean::cnstr_release(x_318, 0);
 lean::cnstr_release(x_318, 1);
 x_323 = x_318;
}
if (lean::obj_tag(x_319) == 0)
{
obj* x_326; obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_309);
lean::dec(x_1);
x_326 = lean::cnstr_get(x_319, 0);
lean::inc(x_326);
if (lean::is_shared(x_319)) {
 lean::dec(x_319);
 x_328 = lean::box(0);
} else {
 lean::cnstr_release(x_319, 0);
 x_328 = x_319;
}
if (lean::is_scalar(x_328)) {
 x_329 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_329 = x_328;
}
lean::cnstr_set(x_329, 0, x_326);
if (lean::is_scalar(x_323)) {
 x_330 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_330 = x_323;
}
lean::cnstr_set(x_330, 0, x_329);
lean::cnstr_set(x_330, 1, x_321);
x_3 = x_330;
goto lbl_4;
}
else
{
obj* x_331; obj* x_332; obj* x_333; obj* x_335; 
if (lean::is_shared(x_319)) {
 lean::dec(x_319);
 x_331 = lean::box(0);
} else {
 lean::cnstr_release(x_319, 0);
 x_331 = x_319;
}
x_332 = _l_s4_lean_s2_ir_s11_check__type(x_309, x_316, x_1, x_321);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_338; obj* x_341; obj* x_342; 
x_338 = lean::cnstr_get(x_333, 0);
lean::inc(x_338);
lean::dec(x_333);
if (lean::is_scalar(x_331)) {
 x_341 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_341 = x_331;
}
lean::cnstr_set(x_341, 0, x_338);
if (lean::is_scalar(x_323)) {
 x_342 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_342 = x_323;
}
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_335);
x_3 = x_342;
goto lbl_4;
}
else
{
obj* x_345; obj* x_347; 
lean::dec(x_333);
lean::dec(x_331);
x_345 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_345);
if (lean::is_scalar(x_323)) {
 x_347 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_347 = x_323;
}
lean::cnstr_set(x_347, 0, x_345);
lean::cnstr_set(x_347, 1, x_335);
x_3 = x_347;
goto lbl_4;
}
}
}
else
{
unsigned char x_349; obj* x_351; obj* x_352; obj* x_354; obj* x_356; 
lean::dec(x_313);
x_349 = 5;
lean::inc(x_1);
x_351 = _l_s4_lean_s2_ir_s11_check__type(x_307, x_349, x_1, x_2);
x_352 = lean::cnstr_get(x_351, 0);
lean::inc(x_352);
x_354 = lean::cnstr_get(x_351, 1);
lean::inc(x_354);
if (lean::is_shared(x_351)) {
 lean::dec(x_351);
 x_356 = lean::box(0);
} else {
 lean::cnstr_release(x_351, 0);
 lean::cnstr_release(x_351, 1);
 x_356 = x_351;
}
if (lean::obj_tag(x_352) == 0)
{
obj* x_359; obj* x_361; obj* x_362; obj* x_363; 
lean::dec(x_309);
lean::dec(x_1);
x_359 = lean::cnstr_get(x_352, 0);
lean::inc(x_359);
if (lean::is_shared(x_352)) {
 lean::dec(x_352);
 x_361 = lean::box(0);
} else {
 lean::cnstr_release(x_352, 0);
 x_361 = x_352;
}
if (lean::is_scalar(x_361)) {
 x_362 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_362 = x_361;
}
lean::cnstr_set(x_362, 0, x_359);
if (lean::is_scalar(x_356)) {
 x_363 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_363 = x_356;
}
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_354);
x_3 = x_363;
goto lbl_4;
}
else
{
obj* x_364; obj* x_365; obj* x_366; obj* x_368; 
if (lean::is_shared(x_352)) {
 lean::dec(x_352);
 x_364 = lean::box(0);
} else {
 lean::cnstr_release(x_352, 0);
 x_364 = x_352;
}
x_365 = _l_s4_lean_s2_ir_s11_check__type(x_309, x_349, x_1, x_354);
x_366 = lean::cnstr_get(x_365, 0);
lean::inc(x_366);
x_368 = lean::cnstr_get(x_365, 1);
lean::inc(x_368);
lean::dec(x_365);
if (lean::obj_tag(x_366) == 0)
{
obj* x_371; obj* x_374; obj* x_375; 
x_371 = lean::cnstr_get(x_366, 0);
lean::inc(x_371);
lean::dec(x_366);
if (lean::is_scalar(x_364)) {
 x_374 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_374 = x_364;
}
lean::cnstr_set(x_374, 0, x_371);
if (lean::is_scalar(x_356)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_356;
}
lean::cnstr_set(x_375, 0, x_374);
lean::cnstr_set(x_375, 1, x_368);
x_3 = x_375;
goto lbl_4;
}
else
{
obj* x_378; obj* x_380; 
lean::dec(x_366);
lean::dec(x_364);
x_378 = _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__5;
lean::inc(x_378);
if (lean::is_scalar(x_356)) {
 x_380 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_380 = x_356;
}
lean::cnstr_set(x_380, 0, x_378);
lean::cnstr_set(x_380, 1, x_368);
x_3 = x_380;
goto lbl_4;
}
}
}
}
default:
{
obj* x_381; obj* x_383; unsigned char x_385; obj* x_387; obj* x_388; obj* x_390; obj* x_392; 
x_381 = lean::cnstr_get(x_0, 0);
lean::inc(x_381);
x_383 = lean::cnstr_get(x_0, 1);
lean::inc(x_383);
x_385 = 11;
lean::inc(x_1);
x_387 = _l_s4_lean_s2_ir_s11_check__type(x_381, x_385, x_1, x_2);
x_388 = lean::cnstr_get(x_387, 0);
lean::inc(x_388);
x_390 = lean::cnstr_get(x_387, 1);
lean::inc(x_390);
if (lean::is_shared(x_387)) {
 lean::dec(x_387);
 x_392 = lean::box(0);
} else {
 lean::cnstr_release(x_387, 0);
 lean::cnstr_release(x_387, 1);
 x_392 = x_387;
}
if (lean::obj_tag(x_388) == 0)
{
obj* x_395; obj* x_397; obj* x_398; obj* x_399; 
lean::dec(x_383);
lean::dec(x_1);
x_395 = lean::cnstr_get(x_388, 0);
lean::inc(x_395);
if (lean::is_shared(x_388)) {
 lean::dec(x_388);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_388, 0);
 x_397 = x_388;
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_395);
if (lean::is_scalar(x_392)) {
 x_399 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_399 = x_392;
}
lean::cnstr_set(x_399, 0, x_398);
lean::cnstr_set(x_399, 1, x_390);
x_3 = x_399;
goto lbl_4;
}
else
{
unsigned char x_402; obj* x_403; 
lean::dec(x_388);
lean::dec(x_392);
x_402 = 5;
x_403 = _l_s4_lean_s2_ir_s11_check__type(x_383, x_402, x_1, x_390);
x_3 = x_403;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_404; obj* x_406; obj* x_408; 
x_404 = lean::cnstr_get(x_3, 0);
lean::inc(x_404);
x_406 = lean::cnstr_get(x_3, 1);
lean::inc(x_406);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_408 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_408 = x_3;
}
if (lean::obj_tag(x_404) == 0)
{
obj* x_409; obj* x_411; obj* x_412; unsigned char x_413; obj* x_414; obj* x_416; obj* x_417; obj* x_418; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; 
x_409 = lean::cnstr_get(x_404, 0);
lean::inc(x_409);
if (lean::is_shared(x_404)) {
 lean::dec(x_404);
 x_411 = lean::box(0);
} else {
 lean::cnstr_release(x_404, 0);
 x_411 = x_404;
}
x_412 = _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(x_0);
x_413 = 0;
x_414 = _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_414);
x_416 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_416, 0, x_414);
lean::cnstr_set(x_416, 1, x_412);
lean::cnstr_set_scalar(x_416, sizeof(void*)*2, x_413);
x_417 = x_416;
x_418 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_418);
x_420 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_420, 0, x_417);
lean::cnstr_set(x_420, 1, x_418);
lean::cnstr_set_scalar(x_420, sizeof(void*)*2, x_413);
x_421 = x_420;
x_422 = lean::alloc_cnstr(1, 0, 0);
;
x_423 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_423, 0, x_421);
lean::cnstr_set(x_423, 1, x_422);
lean::cnstr_set_scalar(x_423, sizeof(void*)*2, x_413);
x_424 = x_423;
x_425 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_425, 0, x_424);
lean::cnstr_set(x_425, 1, x_409);
lean::cnstr_set_scalar(x_425, sizeof(void*)*2, x_413);
x_426 = x_425;
if (lean::is_scalar(x_411)) {
 x_427 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_427 = x_411;
}
lean::cnstr_set(x_427, 0, x_426);
if (lean::is_scalar(x_408)) {
 x_428 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_428 = x_408;
}
lean::cnstr_set(x_428, 0, x_427);
lean::cnstr_set(x_428, 1, x_406);
return x_428;
}
else
{
obj* x_430; 
lean::dec(x_0);
if (lean::is_scalar(x_408)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_408;
}
lean::cnstr_set(x_430, 0, x_404);
lean::cnstr_set(x_430, 1, x_406);
return x_430;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid assignment");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__2() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid unary operation");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__3() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid binary operation");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__4() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("too many arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__5() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid scalar array");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; unsigned char x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = 11;
lean::inc(x_1);
x_15 = _l_s4_lean_s2_ir_s11_check__type(x_8, x_13, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_20 = x_15;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_25 = x_16;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
return x_27;
}
else
{
obj* x_30; 
lean::dec(x_16);
lean::dec(x_20);
x_30 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__1(x_10, x_1, x_18);
return x_30;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; unsigned char x_13; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
lean::dec(x_8);
x_15 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_13);
x_16 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_17 = lean::nat_dec_eq(x_15, x_16);
lean::dec(x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_1);
x_22 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2_s11___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_2);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_17);
x_26 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2(x_10, x_1, x_2);
return x_26;
}
}
}
}
obj* _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid closure, arguments must have type object");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; unsigned char x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = 11;
lean::inc(x_1);
x_15 = _l_s4_lean_s2_ir_s11_check__type(x_8, x_13, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_20 = x_15;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_16, 0);
lean::inc(x_23);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_25 = x_16;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
return x_27;
}
else
{
obj* x_30; 
lean::dec(x_16);
lean::dec(x_20);
x_30 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__3(x_10, x_1, x_18);
return x_30;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_phi_s5_check(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_0);
x_6 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_phi_s5_check_s9___spec__1(x_0, x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_15; unsigned char x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
}
x_15 = _l_s4_lean_s2_ir_s3_phi_s10_to__format_s6___main(x_0);
x_16 = 0;
x_17 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_16);
x_20 = x_19;
x_21 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_16);
x_24 = x_23;
x_25 = lean::alloc_cnstr(1, 0, 0);
;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_16);
x_27 = x_26;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_16);
x_29 = x_28;
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_29);
if (lean::is_scalar(x_11)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_11;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_9);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_0);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_phi_s5_check_s9___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_7 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; unsigned char x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
lean::inc(x_2);
x_17 = _l_s4_lean_s2_ir_s11_check__type(x_10, x_15, x_2, x_3);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 x_22 = x_17;
}
if (lean::obj_tag(x_18) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_18, 0);
lean::inc(x_26);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_28 = x_18;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
if (lean::is_scalar(x_22)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_22;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_20);
return x_30;
}
else
{
obj* x_33; 
lean::dec(x_18);
lean::dec(x_22);
x_33 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_phi_s5_check_s9___spec__1(x_0, x_12, x_2, x_20);
return x_33;
}
}
}
}
obj* _l_s4_lean_s2_ir_s19_check__result__type_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = _l_s4_lean_s2_ir_s11_check__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s19_check__result__type(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = _l_s4_lean_s2_ir_s11_check__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s10_terminator_s5_check(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; unsigned char x_10; obj* x_12; obj* x_13; obj* x_15; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::unbox(x_8);
lean::dec(x_8);
x_12 = _l_s4_lean_s2_ir_s11_check__type(x_6, x_10, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_3 = x_13;
x_4 = x_15;
goto lbl_5;
}
case 1:
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
x_20 = _l_s4_lean_s2_ir_s9_get__type(x_18, x_1, x_2);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_28 = x_21;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
x_3 = x_29;
x_4 = x_23;
goto lbl_5;
}
else
{
obj* x_30; unsigned char x_33; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::unbox(x_30);
lean::dec(x_30);
x_35 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_33);
x_36 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_37 = lean::nat_dec_eq(x_35, x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_37);
x_39 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3;
x_40 = lean::nat_dec_eq(x_35, x_39);
lean::dec(x_35);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; 
lean::dec(x_40);
x_43 = _l_s4_lean_s2_ir_s10_terminator_s5_check_s11___closed__1;
lean::inc(x_43);
x_3 = x_43;
x_4 = x_23;
goto lbl_5;
}
else
{
obj* x_46; 
lean::dec(x_40);
x_46 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_46);
x_3 = x_46;
x_4 = x_23;
goto lbl_5;
}
}
else
{
obj* x_50; 
lean::dec(x_35);
lean::dec(x_37);
x_50 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_50);
x_3 = x_50;
x_4 = x_23;
goto lbl_5;
}
}
}
default:
{
obj* x_53; 
lean::dec(x_1);
x_53 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_53);
x_3 = x_53;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_55; obj* x_57; obj* x_58; unsigned char x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_55 = lean::cnstr_get(x_3, 0);
lean::inc(x_55);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_57 = x_3;
}
x_58 = _l_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main(x_0);
x_59 = 0;
x_60 = _l_s4_lean_s2_ir_s10_terminator_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_59);
x_63 = x_62;
x_64 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_63);
lean::cnstr_set(x_66, 1, x_64);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_59);
x_67 = x_66;
x_68 = lean::alloc_cnstr(1, 0, 0);
;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_59);
x_70 = x_69;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_55);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_59);
x_72 = x_71;
if (lean::is_scalar(x_57)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_57;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_4);
return x_74;
}
else
{
obj* x_76; 
lean::dec(x_0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_3);
lean::cnstr_set(x_76, 1, x_4);
return x_76;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s10_terminator_s5_check_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("variable must be an uint32 or bool");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s5_block_s5_check(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
lean::inc(x_1);
x_11 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__1(x_3, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_7 = x_20;
x_8 = x_14;
goto lbl_9;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_0, 2);
lean::inc(x_22);
lean::inc(x_1);
x_25 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__2(x_22, x_1, x_14);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_7 = x_26;
x_8 = x_28;
goto lbl_9;
}
lbl_9:
{

if (lean::obj_tag(x_7) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_39; unsigned char x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_5);
lean::dec(x_1);
x_33 = lean::cnstr_get(x_7, 0);
lean::inc(x_33);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_35 = x_7;
}
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
x_39 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main_s9___spec__4(x_36);
x_40 = 0;
x_41 = _l_s4_lean_s2_ir_s5_block_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_40);
x_44 = x_43;
x_45 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_40);
x_48 = x_47;
x_49 = lean::alloc_cnstr(1, 0, 0);
;
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_40);
x_51 = x_50;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_33);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_40);
x_53 = x_52;
if (lean::is_scalar(x_35)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_35;
}
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_8);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_62; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_56 = x_7;
}
x_57 = _l_s4_lean_s2_ir_s10_terminator_s5_check(x_5, x_1, x_8);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
}
if (lean::obj_tag(x_58) == 0)
{
obj* x_63; obj* x_66; obj* x_69; unsigned char x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_63 = lean::cnstr_get(x_58, 0);
lean::inc(x_63);
lean::dec(x_58);
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
x_69 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main_s9___spec__4(x_66);
x_70 = 0;
x_71 = _l_s4_lean_s2_ir_s5_block_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_71);
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_70);
x_74 = x_73;
x_75 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_70);
x_78 = x_77;
x_79 = lean::alloc_cnstr(1, 0, 0);
;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_70);
x_81 = x_80;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_63);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_70);
x_83 = x_82;
if (lean::is_scalar(x_56)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_56;
}
lean::cnstr_set(x_84, 0, x_83);
if (lean::is_scalar(x_62)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_62;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_60);
return x_85;
}
else
{
obj* x_88; 
lean::dec(x_56);
lean::dec(x_0);
if (lean::is_scalar(x_62)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_62;
}
lean::cnstr_set(x_88, 0, x_58);
lean::cnstr_set(x_88, 1, x_60);
return x_88;
}
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_phi_s5_check(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s5_instr_s5_check(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_block_s5_check_s9___spec__2(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s5_check_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s5_check_s6___main_s9___spec__1(x_8, x_1, x_2);
return x_11;
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s5_check_s6___main_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s5_block_s5_check(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s4_decl_s5_check_s6___main_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s4_decl_s5_check(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s4_decl_s5_check_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s2_ir_s11_type__check(obj* x_0, obj* x_1) {
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s4_decl_s12_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s11_type__check_s11___lambda__1), 4, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1_s6___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2_s6___rarg), 4, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_6);
x_8 = _l_s4_lean_s2_ir_s11_type__check_s11___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2_s6___rarg), 4, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
x_11 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_12 = lean::cnstr_get(x_11, 2);
lean::inc(x_12);
lean::dec(x_11);
x_15 = _l_s4_lean_s2_ir_s16_type__checker__m_s3_run_s6___rarg(x_10, x_1, x_12);
return x_15;
}
}
obj* _init__l_s4_lean_s2_ir_s11_type__check_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s11_type__check_s11___lambda__2_s7___boxed), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1_s6___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; 
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s4_decl_s5_check_s6___main(x_0, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__2(unsigned char x_0, obj* x_1, obj* x_2) {
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_8 = x_1;
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::apply_3(x_0, x_11, x_2, x_3);
return x_14;
}
}
}
obj* _l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_bind__cont_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__1_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_3(x_1, x_6, x_2, x_8);
return x_11;
}
}
obj* _l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_bind_s4___at_s4_lean_s2_ir_s11_type__check_s9___spec__2_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s11_type__check_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s11_type__check_s11___lambda__2(x_3, x_1, x_2);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_lean_s2_ir_s9_instances();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s6_format();
void _l_initialize__l_s4_init_s7_control_s11_combinators();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s2_ir_s11_type__check() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s2_ir_s9_instances();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s6_format();
 _l_initialize__l_s4_init_s7_control_s11_combinators();
 _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1 = _init__l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1();
 _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1 = _init__l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__1();
 _l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2 = _init__l_s4_lean_s2_ir_s23_is__nonfloat__arith__ty_s11___closed__2();
 _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1 = _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1();
 _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2 = _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__2();
 _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3 = _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__3();
 _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4 = _init__l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4();
 _l_s4_lean_s2_ir_s16_type__checker__m = _init__l_s4_lean_s2_ir_s16_type__checker__m();
 _l_s4_lean_s2_ir_s11_match__type_s11___closed__1 = _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__1();
 _l_s4_lean_s2_ir_s11_match__type_s11___closed__2 = _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__2();
 _l_s4_lean_s2_ir_s11_match__type_s11___closed__3 = _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__3();
 _l_s4_lean_s2_ir_s11_match__type_s11___closed__4 = _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__4();
 _l_s4_lean_s2_ir_s11_match__type_s11___closed__5 = _init__l_s4_lean_s2_ir_s11_match__type_s11___closed__5();
 _l_s4_lean_s2_ir_s9_get__type_s11___closed__1 = _init__l_s4_lean_s2_ir_s9_get__type_s11___closed__1();
 _l_s4_lean_s2_ir_s11_check__type_s11___closed__1 = _init__l_s4_lean_s2_ir_s11_check__type_s11___closed__1();
 _l_s4_lean_s2_ir_s11_check__type_s11___closed__2 = _init__l_s4_lean_s2_ir_s11_check__type_s11___closed__2();
 _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__1 = _init__l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__1();
 _l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__2 = _init__l_s4_lean_s2_ir_s15_check__ne__type_s11___closed__2();
 _l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1 = _init__l_s4_lean_s2_ir_s16_invalid__literal_s6___rarg_s11___closed__1();
 _l_s4_lean_s2_ir_s9_get__decl_s11___closed__1 = _init__l_s4_lean_s2_ir_s9_get__decl_s11___closed__1();
 _l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s17_check__arg__types_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__1 = _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__1();
 _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__2 = _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__2();
 _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__3 = _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__3();
 _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__4 = _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__4();
 _l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__5 = _init__l_s4_lean_s2_ir_s5_instr_s5_check_s11___closed__5();
 _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2_s11___closed__1 = _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s5_instr_s5_check_s9___spec__2_s11___closed__1();
 _l_s4_lean_s2_ir_s10_terminator_s5_check_s11___closed__1 = _init__l_s4_lean_s2_ir_s10_terminator_s5_check_s11___closed__1();
 _l_s4_lean_s2_ir_s11_type__check_s11___closed__1 = _init__l_s4_lean_s2_ir_s11_type__check_s11___closed__1();
}
