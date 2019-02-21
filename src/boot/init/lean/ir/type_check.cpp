// Lean compiler output
// Module: init.lean.ir.type_check
// Imports: init.lean.ir.instances init.lean.ir.format init.control.combinators
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
uint8 l_lean_ir_is__bitwise__ty(uint8);
uint8 l_lean_ir_is__nonfloat__arith__ty(uint8);
uint8 l_lean_ir_is__signed__arith__ty(uint8);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_lean_ir_valid__assign__unop__types___closed__4;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_terminator_check(obj*, obj*, obj*);
obj* l_lean_ir_set__result__types(obj*, obj*, obj*, obj*);
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_lean_ir_match__type(obj*, uint8, uint8, obj*, obj*);
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_lean_ir_match__type___closed__5;
obj* l_lean_ir_check__ne__type(obj*, uint8, obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_set__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_phi_infer__types(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1(obj*, obj*);
obj* l_lean_ir_check__arg__types___main(obj*, obj*, obj*, obj*);
uint8 l_lean_ir_valid__assign__unop__types(uint8, uint8, uint8);
obj* l_lean_ir_type__check___closed__1;
obj* l_lean_ir_decl_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___closed__2;
obj* l_lean_ir_block_check(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(obj*);
obj* l_lean_ir_type_to__format___main(uint8);
obj* l_lean_ir_decl_check___main(obj*, obj*, obj*);
obj* l_lean_ir_type2id___main(uint8);
obj* l_lean_ir_block_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__1;
obj* l_lean_ir_instr_check___closed__3;
obj* l_lean_ir_instr_infer__types(obj*, obj*, obj*);
obj* l_lean_ir_get__decl___closed__1;
obj* l_lean_ir_decl_check(obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___closed__1;
obj* l_lean_ir_valid__assign__unop__types___closed__3;
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__5;
obj* l_lean_ir_invalid__literal___rarg(obj*);
uint8 l_lean_ir_is__arith__ty(uint8);
obj* l_lean_ir_check__type___closed__2;
obj* l_lean_ir_invalid__literal___rarg___closed__1;
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_lean_ir_type__check___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1(obj*, obj*, uint8);
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_header___main(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_is__bitshift__ty___boxed(obj*);
obj* l_lean_ir_instr_check(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1(obj*, obj*);
obj* l_lean_ir_phi_to__format___main(obj*);
obj* l_lean_ir_get__type(obj*, obj*, obj*);
obj* l_lean_ir_check__ne__type___closed__2;
obj* l_lean_ir_type__checker__m;
obj* l_lean_ir_match__type___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__2;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_lean_ir_is__bitshift__ty(uint8);
obj* l_lean_ir_type__checker__m_run___rarg(obj*, obj*, obj*);
obj* l_lean_ir_infer__types(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2(obj*, obj*, uint8);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_instr_check___closed__4;
obj* l_lean_ir_valid__assign__unop__types___closed__2;
obj* l_lean_ir_decl_infer__types___main(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__4;
obj* l_lean_ir_type__checker__m_run(obj*);
obj* l_lean_ir_get__decl(obj*, obj*, obj*);
uint8 l_lean_ir_valid__assign__binop__types(uint8, uint8, uint8, uint8);
obj* l_lean_ir_match__type___closed__3;
obj* l_lean_ir_check__arg__types(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
extern obj* l_int_zero;
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_ir_invalid__literal(obj*);
obj* l_lean_ir_set__result__types___main(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_valid__assign__binop__types___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_check__type(obj*, uint8, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3(obj*, obj*, uint8);
obj* l_lean_ir_instr_check___closed__2;
obj* l_lean_ir_check__result__type___main(obj*, obj*, obj*, obj*);
obj* l_lean_ir_get__type___closed__1;
obj* l_lean_ir_terminator_check___closed__1;
obj* l_lean_ir_is__arith__ty___boxed(obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_phi_check(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___boxed(obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2(obj*);
obj* l_lean_ir_check__arg__types___main___closed__1;
obj* l_lean_ir_check__result__type(obj*, obj*, obj*, obj*);
extern obj* l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_set__type(obj*, uint8, obj*, obj*);
obj* l_lean_ir_valid__assign__unop__types___closed__1;
obj* l_lean_ir_valid__assign__unop__types___boxed(obj*, obj*, obj*);
obj* l_lean_ir_literal_check___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_is__signed__arith__ty___boxed(obj*);
obj* l_lean_ir_type__check(obj*, obj*);
obj* l_lean_ir_check__type___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__context;
obj* l_lean_ir_literal_check(obj*, uint8, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_ir_type__check___lambda__2(obj*, obj*, obj*);
obj* l_lean_ir_match__type___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_check__type___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_is__bitwise__ty___boxed(obj*);
obj* l_lean_ir_is__nonfloat__arith__ty___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(obj*, obj*, obj*);
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2(obj*, obj*);
obj* l_lean_ir_is__arith__ty___closed__1;
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_lean_ir_arg_infer__types(obj*, obj*, obj*);
extern obj* l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
uint8 l_lean_ir_is__signed__arith__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 6:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
case 7:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
case 8:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
case 9:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
case 10:
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
default:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
}
obj* l_lean_ir_is__signed__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__signed__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_is__arith__ty___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 0;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_is__arith__ty(uint8 x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_lean_ir_type2id___main(x_0);
x_2 = l_lean_ir_is__arith__ty___closed__1;
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_lean_ir_is__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_is__nonfloat__arith__ty___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 10;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_is__nonfloat__arith__ty___closed__2() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 9;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_is__nonfloat__arith__ty(uint8 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_is__arith__ty(x_0);
if (x_1 == 0)
{
if (x_1 == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
if (x_4 == 0)
{
return x_1;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = l_lean_ir_type2id___main(x_0);
x_8 = l_lean_ir_is__nonfloat__arith__ty___closed__2;
x_9 = lean::nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
if (x_1 == 0)
{
lean::dec(x_7);
return x_1;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_12 = lean::nat_dec_eq(x_7, x_11);
lean::dec(x_7);
if (x_12 == 0)
{
return x_1;
}
else
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
}
}
else
{
uint8 x_16; 
lean::dec(x_7);
x_16 = 0;
return x_16;
}
}
}
}
obj* l_lean_ir_is__nonfloat__arith__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__nonfloat__arith__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_ir_is__bitwise__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 6:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 7:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 8:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 9:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 10:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
default:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
}
obj* l_lean_ir_is__bitwise__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__bitwise__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_ir_is__bitshift__ty(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 9:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 10:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 11:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_lean_ir_is__bitshift__ty___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_is__bitshift__ty(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__1() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 11;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__2() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 5;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__3() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 3;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_valid__assign__unop__types___closed__4() {
_start:
{
uint8 x_0; obj* x_1; 
x_0 = 7;
x_1 = l_lean_ir_type2id___main(x_0);
return x_1;
}
}
uint8 l_lean_ir_valid__assign__unop__types(uint8 x_0, uint8 x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; 
switch (x_0) {
case 0:
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = l_lean_ir_type2id___main(x_2);
x_14 = l_lean_ir_type2id___main(x_1);
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_14);
lean::dec(x_13);
if (x_15 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = l_lean_ir_is__bitwise__ty(x_2);
return x_19;
}
}
case 1:
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = l_lean_ir_type2id___main(x_2);
x_21 = l_lean_ir_type2id___main(x_1);
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_21);
lean::dec(x_20);
if (x_22 == 0)
{
uint8 x_25; 
x_25 = 0;
return x_25;
}
else
{
uint8 x_26; 
x_26 = l_lean_ir_is__signed__arith__ty(x_2);
return x_26;
}
}
case 2:
{
obj* x_27; 
x_27 = lean::box(0);
x_3 = x_27;
goto lbl_4;
}
case 3:
{
obj* x_28; 
x_28 = lean::box(0);
x_3 = x_28;
goto lbl_4;
}
case 7:
{
obj* x_29; obj* x_30; uint8 x_31; 
x_29 = l_lean_ir_type2id___main(x_1);
x_30 = l_lean_ir_valid__assign__unop__types___closed__1;
x_31 = lean::nat_dec_eq(x_29, x_30);
lean::dec(x_29);
if (x_31 == 0)
{
uint8 x_33; 
x_33 = 1;
return x_33;
}
else
{
uint8 x_34; 
x_34 = 0;
return x_34;
}
}
case 8:
{
obj* x_35; obj* x_36; uint8 x_37; 
x_35 = l_lean_ir_type2id___main(x_1);
x_36 = l_lean_ir_valid__assign__unop__types___closed__1;
x_37 = lean::nat_dec_eq(x_35, x_36);
lean::dec(x_35);
if (x_37 == 0)
{
uint8 x_39; 
x_39 = 0;
return x_39;
}
else
{
obj* x_40; obj* x_41; uint8 x_42; 
x_40 = l_lean_ir_type2id___main(x_2);
x_41 = l_lean_ir_valid__assign__unop__types___closed__3;
x_42 = lean::nat_dec_eq(x_40, x_41);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = l_lean_ir_valid__assign__unop__types___closed__4;
x_44 = lean::nat_dec_eq(x_40, x_43);
lean::dec(x_40);
if (x_44 == 0)
{
uint8 x_46; 
x_46 = 0;
return x_46;
}
else
{
uint8 x_47; 
x_47 = 1;
return x_47;
}
}
else
{
uint8 x_49; 
lean::dec(x_40);
x_49 = 1;
return x_49;
}
}
}
case 9:
{
obj* x_50; obj* x_51; uint8 x_52; 
x_50 = l_lean_ir_type2id___main(x_2);
x_51 = l_lean_ir_valid__assign__unop__types___closed__1;
x_52 = lean::nat_dec_eq(x_50, x_51);
lean::dec(x_50);
if (x_52 == 0)
{
uint8 x_54; 
x_54 = 0;
return x_54;
}
else
{
obj* x_55; obj* x_56; uint8 x_57; 
x_55 = l_lean_ir_type2id___main(x_1);
x_56 = l_lean_ir_valid__assign__unop__types___closed__3;
x_57 = lean::nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
obj* x_58; uint8 x_59; 
x_58 = l_lean_ir_valid__assign__unop__types___closed__4;
x_59 = lean::nat_dec_eq(x_55, x_58);
lean::dec(x_55);
if (x_59 == 0)
{
uint8 x_61; 
x_61 = 0;
return x_61;
}
else
{
uint8 x_62; 
x_62 = 1;
return x_62;
}
}
else
{
uint8 x_64; 
lean::dec(x_55);
x_64 = 1;
return x_64;
}
}
}
case 10:
{
obj* x_65; 
x_65 = lean::box(0);
x_7 = x_65;
goto lbl_8;
}
case 11:
{
obj* x_66; 
x_66 = lean::box(0);
x_7 = x_66;
goto lbl_8;
}
case 12:
{
obj* x_67; 
x_67 = lean::box(0);
x_9 = x_67;
goto lbl_10;
}
case 13:
{
obj* x_68; 
x_68 = lean::box(0);
x_9 = x_68;
goto lbl_10;
}
case 14:
{
obj* x_69; 
x_69 = lean::box(0);
x_9 = x_69;
goto lbl_10;
}
case 15:
{
obj* x_70; obj* x_71; uint8 x_72; 
x_70 = l_lean_ir_type2id___main(x_1);
x_71 = l_lean_ir_valid__assign__unop__types___closed__1;
x_72 = lean::nat_dec_eq(x_70, x_71);
lean::dec(x_70);
if (x_72 == 0)
{
uint8 x_74; 
x_74 = 0;
return x_74;
}
else
{
obj* x_75; uint8 x_76; 
x_75 = l_lean_ir_type2id___main(x_2);
x_76 = lean::nat_dec_eq(x_75, x_71);
lean::dec(x_75);
if (x_76 == 0)
{
uint8 x_78; 
x_78 = 0;
return x_78;
}
else
{
uint8 x_79; 
x_79 = 1;
return x_79;
}
}
}
case 16:
{
obj* x_80; 
x_80 = lean::box(0);
x_11 = x_80;
goto lbl_12;
}
case 17:
{
obj* x_81; 
x_81 = lean::box(0);
x_11 = x_81;
goto lbl_12;
}
default:
{
obj* x_82; 
x_82 = lean::box(0);
x_5 = x_82;
goto lbl_6;
}
}
lbl_4:
{
obj* x_84; obj* x_85; uint8 x_86; 
lean::dec(x_3);
x_84 = l_lean_ir_type2id___main(x_2);
x_85 = l_lean_ir_type2id___main(x_1);
x_86 = lean::nat_dec_eq(x_84, x_85);
lean::dec(x_85);
if (x_86 == 0)
{
uint8 x_89; 
lean::dec(x_84);
x_89 = 0;
return x_89;
}
else
{
obj* x_90; uint8 x_91; 
x_90 = l_lean_ir_valid__assign__unop__types___closed__1;
x_91 = lean::nat_dec_eq(x_84, x_90);
lean::dec(x_84);
if (x_91 == 0)
{
uint8 x_93; 
x_93 = 0;
return x_93;
}
else
{
uint8 x_94; 
x_94 = 1;
return x_94;
}
}
}
lbl_6:
{
obj* x_96; obj* x_97; uint8 x_98; 
lean::dec(x_5);
x_96 = l_lean_ir_type2id___main(x_2);
x_97 = l_lean_ir_valid__assign__unop__types___closed__1;
x_98 = lean::nat_dec_eq(x_96, x_97);
lean::dec(x_96);
if (x_98 == 0)
{
uint8 x_100; 
x_100 = 0;
return x_100;
}
else
{
obj* x_101; obj* x_102; uint8 x_103; 
x_101 = l_lean_ir_type2id___main(x_1);
x_102 = l_lean_ir_is__arith__ty___closed__1;
x_103 = lean::nat_dec_eq(x_101, x_102);
lean::dec(x_101);
if (x_103 == 0)
{
uint8 x_105; 
x_105 = 0;
return x_105;
}
else
{
uint8 x_106; 
x_106 = 1;
return x_106;
}
}
}
lbl_8:
{
obj* x_108; obj* x_109; uint8 x_110; 
lean::dec(x_7);
x_108 = l_lean_ir_type2id___main(x_2);
x_109 = l_lean_ir_valid__assign__unop__types___closed__1;
x_110 = lean::nat_dec_eq(x_108, x_109);
lean::dec(x_108);
if (x_110 == 0)
{
uint8 x_112; 
x_112 = 0;
return x_112;
}
else
{
obj* x_113; uint8 x_114; 
x_113 = l_lean_ir_type2id___main(x_1);
x_114 = lean::nat_dec_eq(x_113, x_109);
lean::dec(x_113);
if (x_114 == 0)
{
uint8 x_116; 
x_116 = 0;
return x_116;
}
else
{
uint8 x_117; 
x_117 = 1;
return x_117;
}
}
}
lbl_10:
{
obj* x_119; obj* x_120; uint8 x_121; 
lean::dec(x_9);
x_119 = l_lean_ir_type2id___main(x_1);
x_120 = l_lean_ir_valid__assign__unop__types___closed__2;
x_121 = lean::nat_dec_eq(x_119, x_120);
lean::dec(x_119);
if (x_121 == 0)
{
uint8 x_123; 
x_123 = 0;
return x_123;
}
else
{
obj* x_124; obj* x_125; uint8 x_126; 
x_124 = l_lean_ir_type2id___main(x_2);
x_125 = l_lean_ir_valid__assign__unop__types___closed__1;
x_126 = lean::nat_dec_eq(x_124, x_125);
lean::dec(x_124);
if (x_126 == 0)
{
uint8 x_128; 
x_128 = 0;
return x_128;
}
else
{
uint8 x_129; 
x_129 = 1;
return x_129;
}
}
}
lbl_12:
{
obj* x_131; obj* x_132; uint8 x_133; 
lean::dec(x_11);
x_131 = l_lean_ir_type2id___main(x_1);
x_132 = l_lean_ir_valid__assign__unop__types___closed__3;
x_133 = lean::nat_dec_eq(x_131, x_132);
lean::dec(x_131);
if (x_133 == 0)
{
uint8 x_135; 
x_135 = 0;
return x_135;
}
else
{
obj* x_136; obj* x_137; uint8 x_138; 
x_136 = l_lean_ir_type2id___main(x_2);
x_137 = l_lean_ir_valid__assign__unop__types___closed__1;
x_138 = lean::nat_dec_eq(x_136, x_137);
lean::dec(x_136);
if (x_138 == 0)
{
uint8 x_140; 
x_140 = 0;
return x_140;
}
else
{
uint8 x_141; 
x_141 = 1;
return x_141;
}
}
}
}
}
obj* l_lean_ir_valid__assign__unop__types___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; uint8 x_6; obj* x_7; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = l_lean_ir_valid__assign__unop__types(x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
uint8 l_lean_ir_valid__assign__binop__types(uint8 x_0, uint8 x_1, uint8 x_2, uint8 x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
switch (x_0) {
case 0:
{
obj* x_18; 
x_18 = lean::box(0);
x_4 = x_18;
goto lbl_5;
}
case 1:
{
obj* x_19; 
x_19 = lean::box(0);
x_4 = x_19;
goto lbl_5;
}
case 2:
{
obj* x_20; 
x_20 = lean::box(0);
x_4 = x_20;
goto lbl_5;
}
case 3:
{
obj* x_21; 
x_21 = lean::box(0);
x_4 = x_21;
goto lbl_5;
}
case 4:
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = l_lean_ir_type2id___main(x_1);
x_23 = l_lean_ir_type2id___main(x_2);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
uint8 x_27; 
lean::dec(x_22);
x_27 = 0;
return x_27;
}
else
{
obj* x_28; uint8 x_29; 
x_28 = l_lean_ir_type2id___main(x_3);
x_29 = lean::nat_dec_eq(x_22, x_28);
lean::dec(x_28);
lean::dec(x_22);
if (x_29 == 0)
{
uint8 x_32; 
x_32 = 0;
return x_32;
}
else
{
uint8 x_33; 
x_33 = l_lean_ir_is__nonfloat__arith__ty(x_1);
return x_33;
}
}
}
case 10:
{
obj* x_34; 
x_34 = lean::box(0);
x_8 = x_34;
goto lbl_9;
}
case 11:
{
obj* x_35; 
x_35 = lean::box(0);
x_8 = x_35;
goto lbl_9;
}
case 12:
{
obj* x_36; 
x_36 = lean::box(0);
x_10 = x_36;
goto lbl_11;
}
case 13:
{
obj* x_37; 
x_37 = lean::box(0);
x_10 = x_37;
goto lbl_11;
}
case 14:
{
obj* x_38; 
x_38 = lean::box(0);
x_10 = x_38;
goto lbl_11;
}
case 15:
{
obj* x_39; 
x_39 = lean::box(0);
x_12 = x_39;
goto lbl_13;
}
case 16:
{
obj* x_40; 
x_40 = lean::box(0);
x_12 = x_40;
goto lbl_13;
}
case 17:
{
obj* x_41; 
x_41 = lean::box(0);
x_14 = x_41;
goto lbl_15;
}
case 18:
{
obj* x_42; 
x_42 = lean::box(0);
x_14 = x_42;
goto lbl_15;
}
case 19:
{
obj* x_43; 
x_43 = lean::box(0);
x_16 = x_43;
goto lbl_17;
}
case 20:
{
obj* x_44; 
x_44 = lean::box(0);
x_16 = x_44;
goto lbl_17;
}
case 21:
{
obj* x_45; 
x_45 = lean::box(0);
x_16 = x_45;
goto lbl_17;
}
case 22:
{
obj* x_46; 
x_46 = lean::box(0);
x_16 = x_46;
goto lbl_17;
}
case 23:
{
obj* x_47; obj* x_48; uint8 x_49; 
x_47 = l_lean_ir_type2id___main(x_2);
x_48 = l_lean_ir_valid__assign__unop__types___closed__1;
x_49 = lean::nat_dec_eq(x_47, x_48);
lean::dec(x_47);
if (x_49 == 0)
{
uint8 x_51; 
x_51 = 0;
return x_51;
}
else
{
obj* x_52; obj* x_53; uint8 x_54; 
x_52 = l_lean_ir_type2id___main(x_3);
x_53 = l_lean_ir_valid__assign__unop__types___closed__2;
x_54 = lean::nat_dec_eq(x_52, x_53);
lean::dec(x_52);
if (x_54 == 0)
{
uint8 x_56; 
x_56 = 0;
return x_56;
}
else
{
uint8 x_57; 
x_57 = 1;
return x_57;
}
}
}
case 24:
{
obj* x_58; obj* x_59; uint8 x_60; 
x_58 = l_lean_ir_type2id___main(x_1);
x_59 = l_lean_ir_valid__assign__unop__types___closed__1;
x_60 = lean::nat_dec_eq(x_58, x_59);
lean::dec(x_58);
if (x_60 == 0)
{
uint8 x_62; 
x_62 = 0;
return x_62;
}
else
{
obj* x_63; uint8 x_64; 
x_63 = l_lean_ir_type2id___main(x_2);
x_64 = lean::nat_dec_eq(x_63, x_59);
lean::dec(x_63);
if (x_64 == 0)
{
uint8 x_66; 
x_66 = 0;
return x_66;
}
else
{
uint8 x_67; 
x_67 = 1;
return x_67;
}
}
}
case 25:
{
obj* x_68; obj* x_69; uint8 x_70; 
x_68 = l_lean_ir_type2id___main(x_1);
x_69 = l_lean_ir_valid__assign__unop__types___closed__1;
x_70 = lean::nat_dec_eq(x_68, x_69);
lean::dec(x_68);
if (x_70 == 0)
{
uint8 x_72; 
x_72 = 0;
return x_72;
}
else
{
obj* x_73; uint8 x_74; 
x_73 = l_lean_ir_type2id___main(x_2);
x_74 = lean::nat_dec_eq(x_73, x_69);
lean::dec(x_73);
if (x_74 == 0)
{
uint8 x_76; 
x_76 = 0;
return x_76;
}
else
{
obj* x_77; obj* x_78; uint8 x_79; 
x_77 = l_lean_ir_type2id___main(x_3);
x_78 = l_lean_ir_valid__assign__unop__types___closed__3;
x_79 = lean::nat_dec_eq(x_77, x_78);
lean::dec(x_77);
if (x_79 == 0)
{
uint8 x_81; 
x_81 = 0;
return x_81;
}
else
{
uint8 x_82; 
x_82 = 1;
return x_82;
}
}
}
}
case 26:
{
obj* x_83; obj* x_84; uint8 x_85; 
x_83 = l_lean_ir_type2id___main(x_1);
x_84 = l_lean_ir_valid__assign__unop__types___closed__1;
x_85 = lean::nat_dec_eq(x_83, x_84);
lean::dec(x_83);
if (x_85 == 0)
{
uint8 x_87; 
x_87 = 0;
return x_87;
}
else
{
obj* x_88; uint8 x_89; 
x_88 = l_lean_ir_type2id___main(x_2);
x_89 = lean::nat_dec_eq(x_88, x_84);
lean::dec(x_88);
if (x_89 == 0)
{
uint8 x_91; 
x_91 = 0;
return x_91;
}
else
{
obj* x_92; uint8 x_93; 
x_92 = l_lean_ir_type2id___main(x_3);
x_93 = lean::nat_dec_eq(x_92, x_84);
lean::dec(x_92);
if (x_93 == 0)
{
uint8 x_95; 
x_95 = 0;
return x_95;
}
else
{
uint8 x_96; 
x_96 = 1;
return x_96;
}
}
}
}
default:
{
obj* x_97; 
x_97 = lean::box(0);
x_6 = x_97;
goto lbl_7;
}
}
lbl_5:
{
obj* x_99; obj* x_100; uint8 x_101; 
lean::dec(x_4);
x_99 = l_lean_ir_type2id___main(x_1);
x_100 = l_lean_ir_type2id___main(x_2);
x_101 = lean::nat_dec_eq(x_99, x_100);
lean::dec(x_100);
if (x_101 == 0)
{
uint8 x_104; 
lean::dec(x_99);
x_104 = 0;
return x_104;
}
else
{
obj* x_105; uint8 x_106; 
x_105 = l_lean_ir_type2id___main(x_3);
x_106 = lean::nat_dec_eq(x_99, x_105);
lean::dec(x_105);
lean::dec(x_99);
if (x_106 == 0)
{
uint8 x_109; 
x_109 = 0;
return x_109;
}
else
{
uint8 x_110; 
x_110 = l_lean_ir_is__arith__ty(x_1);
return x_110;
}
}
}
lbl_7:
{
obj* x_112; obj* x_113; uint8 x_114; 
lean::dec(x_6);
x_112 = l_lean_ir_type2id___main(x_1);
x_113 = l_lean_ir_type2id___main(x_2);
x_114 = lean::nat_dec_eq(x_112, x_113);
lean::dec(x_113);
if (x_114 == 0)
{
uint8 x_117; 
lean::dec(x_112);
x_117 = 0;
return x_117;
}
else
{
obj* x_118; uint8 x_119; 
x_118 = l_lean_ir_type2id___main(x_3);
x_119 = lean::nat_dec_eq(x_112, x_118);
lean::dec(x_118);
if (x_119 == 0)
{
uint8 x_122; 
lean::dec(x_112);
x_122 = 0;
return x_122;
}
else
{
obj* x_123; uint8 x_124; 
x_123 = l_lean_ir_valid__assign__unop__types___closed__1;
x_124 = lean::nat_dec_eq(x_112, x_123);
lean::dec(x_112);
if (x_124 == 0)
{
uint8 x_126; 
x_126 = 0;
return x_126;
}
else
{
uint8 x_127; 
x_127 = 1;
return x_127;
}
}
}
}
lbl_9:
{
obj* x_129; obj* x_130; uint8 x_131; 
lean::dec(x_8);
x_129 = l_lean_ir_type2id___main(x_1);
x_130 = l_lean_ir_type2id___main(x_2);
x_131 = lean::nat_dec_eq(x_129, x_130);
lean::dec(x_130);
if (x_131 == 0)
{
uint8 x_134; 
lean::dec(x_129);
x_134 = 0;
return x_134;
}
else
{
obj* x_135; uint8 x_136; 
x_135 = l_lean_ir_type2id___main(x_3);
x_136 = lean::nat_dec_eq(x_129, x_135);
lean::dec(x_135);
lean::dec(x_129);
if (x_136 == 0)
{
uint8 x_139; 
x_139 = 0;
return x_139;
}
else
{
uint8 x_140; 
x_140 = l_lean_ir_is__bitshift__ty(x_1);
return x_140;
}
}
}
lbl_11:
{
obj* x_142; obj* x_143; uint8 x_144; 
lean::dec(x_10);
x_142 = l_lean_ir_type2id___main(x_1);
x_143 = l_lean_ir_type2id___main(x_2);
x_144 = lean::nat_dec_eq(x_142, x_143);
lean::dec(x_143);
if (x_144 == 0)
{
uint8 x_147; 
lean::dec(x_142);
x_147 = 0;
return x_147;
}
else
{
obj* x_148; uint8 x_149; 
x_148 = l_lean_ir_type2id___main(x_3);
x_149 = lean::nat_dec_eq(x_142, x_148);
lean::dec(x_148);
lean::dec(x_142);
if (x_149 == 0)
{
uint8 x_152; 
x_152 = 0;
return x_152;
}
else
{
uint8 x_153; 
x_153 = l_lean_ir_is__bitwise__ty(x_1);
return x_153;
}
}
}
lbl_13:
{
obj* x_155; obj* x_156; uint8 x_157; 
lean::dec(x_12);
x_155 = l_lean_ir_type2id___main(x_1);
x_156 = l_lean_ir_is__arith__ty___closed__1;
x_157 = lean::nat_dec_eq(x_155, x_156);
lean::dec(x_155);
if (x_157 == 0)
{
uint8 x_159; 
x_159 = 0;
return x_159;
}
else
{
obj* x_160; obj* x_161; uint8 x_162; 
x_160 = l_lean_ir_type2id___main(x_2);
x_161 = l_lean_ir_type2id___main(x_3);
x_162 = lean::nat_dec_eq(x_160, x_161);
lean::dec(x_161);
lean::dec(x_160);
if (x_162 == 0)
{
uint8 x_165; 
x_165 = 0;
return x_165;
}
else
{
uint8 x_166; 
x_166 = l_lean_ir_is__arith__ty(x_2);
return x_166;
}
}
}
lbl_15:
{
obj* x_168; obj* x_169; uint8 x_170; 
lean::dec(x_14);
x_168 = l_lean_ir_type2id___main(x_1);
x_169 = l_lean_ir_is__arith__ty___closed__1;
x_170 = lean::nat_dec_eq(x_168, x_169);
lean::dec(x_168);
if (x_170 == 0)
{
uint8 x_172; 
x_172 = 0;
return x_172;
}
else
{
obj* x_173; obj* x_174; uint8 x_175; 
x_173 = l_lean_ir_type2id___main(x_2);
x_174 = l_lean_ir_type2id___main(x_3);
x_175 = lean::nat_dec_eq(x_173, x_174);
lean::dec(x_174);
lean::dec(x_173);
if (x_175 == 0)
{
uint8 x_178; 
x_178 = 0;
return x_178;
}
else
{
uint8 x_179; 
x_179 = 1;
return x_179;
}
}
}
lbl_17:
{
obj* x_181; obj* x_182; uint8 x_183; 
lean::dec(x_16);
x_181 = l_lean_ir_type2id___main(x_1);
x_182 = l_lean_ir_is__arith__ty___closed__1;
x_183 = lean::nat_dec_eq(x_181, x_182);
lean::dec(x_181);
if (x_183 == 0)
{
uint8 x_185; 
x_185 = 0;
return x_185;
}
else
{
obj* x_186; obj* x_187; uint8 x_188; 
x_186 = l_lean_ir_type2id___main(x_2);
x_187 = l_lean_ir_type2id___main(x_3);
x_188 = lean::nat_dec_eq(x_186, x_187);
lean::dec(x_187);
if (x_188 == 0)
{
uint8 x_191; 
lean::dec(x_186);
x_191 = 0;
return x_191;
}
else
{
obj* x_192; uint8 x_193; 
x_192 = l_lean_ir_valid__assign__unop__types___closed__1;
x_193 = lean::nat_dec_eq(x_186, x_192);
lean::dec(x_186);
if (x_193 == 0)
{
uint8 x_195; 
x_195 = 0;
return x_195;
}
else
{
uint8 x_196; 
x_196 = 1;
return x_196;
}
}
}
}
}
}
obj* l_lean_ir_valid__assign__binop__types___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; uint8 x_6; uint8 x_7; uint8 x_8; obj* x_9; 
x_4 = lean::unbox(x_0);
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = lean::unbox(x_3);
x_8 = l_lean_ir_valid__assign__binop__types(x_4, x_5, x_6, x_7);
x_9 = lean::box(x_8);
return x_9;
}
}
obj* _init_l_lean_ir_type__checker__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_ir_type__checker__m_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_lean_ir_mk__context;
x_5 = lean::apply_2(x_0, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_ir_type__checker__m_run(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__checker__m_run___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_lean_ir_match__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type mismatch, variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` has type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("`");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", but is expected to have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_match__type___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_match__type(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
lean::dec(x_3);
x_6 = l_lean_ir_type2id___main(x_1);
x_7 = l_lean_ir_type2id___main(x_2);
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_11 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_12 = 0;
x_13 = l_lean_ir_match__type___closed__1;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = l_lean_ir_match__type___closed__2;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_12);
x_18 = x_17;
x_19 = l_lean_ir_type_to__format___main(x_1);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_12);
x_21 = x_20;
x_22 = l_lean_ir_match__type___closed__3;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_12);
x_24 = x_23;
x_25 = l_lean_ir_match__type___closed__4;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_12);
x_27 = x_26;
x_28 = l_lean_ir_type_to__format___main(x_2);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_12);
x_30 = x_29;
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_12);
x_32 = x_31;
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_4);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_0);
x_36 = l_lean_ir_match__type___closed__5;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_4);
return x_37;
}
}
}
obj* l_lean_ir_match__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; uint8 x_6; obj* x_7; 
x_5 = lean::unbox(x_1);
x_6 = lean::unbox(x_2);
x_7 = l_lean_ir_match__type(x_0, x_5, x_6, x_3, x_4);
return x_7;
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_19; uint8 x_20; 
lean::dec(x_4);
lean::inc(x_1);
x_19 = l_lean_name_quick__lt___main(x_6, x_1);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; 
lean::dec(x_10);
lean::dec(x_1);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_8);
return x_23;
}
else
{
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_6);
x_0 = x_4;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_ir_get__type___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_ir_get__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("undefined variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_get__type(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_1);
lean::inc(x_0);
lean::inc(x_2);
x_6 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_2, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_8 = 0;
x_9 = l_lean_ir_get__type___closed__1;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = x_10;
x_12 = l_lean_ir_match__type___closed__3;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_8);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
lean::dec(x_6);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_2);
return x_22;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = 0;
x_4 = lean::box(x_2);
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_0);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_3);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; uint8 x_20; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
x_12 = lean::cnstr_get(x_0, 2);
x_14 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_16 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
lean::inc(x_10);
lean::inc(x_1);
x_19 = l_lean_name_quick__lt___main(x_1, x_10);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; uint8 x_24; 
lean::inc(x_1);
lean::inc(x_10);
x_23 = l_lean_name_quick__lt___main(x_10, x_1);
x_24 = lean::unbox(x_23);
if (x_24 == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_10);
lean::dec(x_12);
x_27 = lean::box(x_2);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_8);
lean::cnstr_set(x_28, 1, x_1);
lean::cnstr_set(x_28, 2, x_27);
lean::cnstr_set(x_28, 3, x_14);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_7);
x_29 = x_28;
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_14, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_16;
}
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
lean::cnstr_set(x_31, 2, x_12);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_7);
x_32 = x_31;
return x_32;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_8, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_16;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_10);
lean::cnstr_set(x_34, 2, x_12);
lean::cnstr_set(x_34, 3, x_14);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_7);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_47; uint8 x_48; 
x_36 = lean::cnstr_get(x_0, 0);
x_38 = lean::cnstr_get(x_0, 1);
x_40 = lean::cnstr_get(x_0, 2);
x_42 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_44 = x_0;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_0);
 x_44 = lean::box(0);
}
lean::inc(x_38);
lean::inc(x_1);
x_47 = l_lean_name_quick__lt___main(x_1, x_38);
x_48 = lean::unbox(x_47);
if (x_48 == 0)
{
obj* x_51; uint8 x_52; 
lean::inc(x_1);
lean::inc(x_38);
x_51 = l_lean_name_quick__lt___main(x_38, x_1);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_38);
lean::dec(x_40);
x_55 = lean::box(x_2);
if (lean::is_scalar(x_44)) {
 x_56 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_56 = x_44;
}
lean::cnstr_set(x_56, 0, x_36);
lean::cnstr_set(x_56, 1, x_1);
lean::cnstr_set(x_56, 2, x_55);
lean::cnstr_set(x_56, 3, x_42);
lean::cnstr_set_scalar(x_56, sizeof(void*)*4, x_7);
x_57 = x_56;
return x_57;
}
else
{
uint8 x_59; 
lean::inc(x_42);
x_59 = l_rbnode_is__red___main___rarg(x_42);
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_42, x_1, x_2);
if (lean::is_scalar(x_44)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_44;
}
lean::cnstr_set(x_61, 0, x_36);
lean::cnstr_set(x_61, 1, x_38);
lean::cnstr_set(x_61, 2, x_40);
lean::cnstr_set(x_61, 3, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_7);
x_62 = x_61;
return x_62;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_63 = lean::box(0);
if (lean::is_scalar(x_44)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_44;
}
lean::cnstr_set(x_64, 0, x_36);
lean::cnstr_set(x_64, 1, x_38);
lean::cnstr_set(x_64, 2, x_40);
lean::cnstr_set(x_64, 3, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_7);
x_65 = x_64;
x_66 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_42, x_1, x_2);
x_67 = l_rbnode_balance2___main___rarg(x_65, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_is__red___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_44)) {
 x_71 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_71 = x_44;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_38);
lean::cnstr_set(x_71, 2, x_40);
lean::cnstr_set(x_71, 3, x_42);
lean::cnstr_set_scalar(x_71, sizeof(void*)*4, x_7);
x_72 = x_71;
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::box(0);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_7);
x_75 = x_74;
x_76 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_36, x_1, x_2);
x_77 = l_rbnode_balance1___main___rarg(x_75, x_76);
return x_77;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
uint8 x_4; 
lean::inc(x_0);
x_4 = l_rbnode_is__red___main___rarg(x_0);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_2);
x_7 = l_rbnode_set__black___main___rarg(x_6);
return x_7;
}
}
}
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_set__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::inc(x_0);
lean::inc(x_3);
x_6 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_8 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_3, x_0, x_1);
x_9 = l_lean_ir_match__type___closed__5;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
else
{
obj* x_11; uint8 x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::unbox(x_11);
x_15 = l_lean_ir_match__type(x_0, x_14, x_1, x_2, x_3);
return x_15;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_3);
return x_4;
}
}
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_0, x_1, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_rbmap_insert___main___at_lean_ir_set__type___spec__1(x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_ir_set__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_check__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("type for variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_check__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` is not available");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::inc(x_0);
lean::inc(x_3);
x_6 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_9 = 0;
x_10 = l_lean_ir_check__type___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_lean_ir_check__type___closed__2;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
else
{
obj* x_18; uint8 x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
lean::dec(x_6);
x_21 = lean::unbox(x_18);
x_22 = l_lean_ir_match__type(x_0, x_21, x_1, x_2, x_3);
return x_22;
}
}
}
obj* l_lean_ir_check__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_check__ne__type___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("variable `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_check__ne__type___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("` must not have type `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__ne__type(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::inc(x_0);
lean::inc(x_3);
x_7 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_3, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_9 = 0;
x_10 = l_lean_ir_check__type___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_lean_ir_check__type___closed__2;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
else
{
obj* x_18; uint8 x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
lean::dec(x_7);
x_21 = lean::unbox(x_18);
x_22 = l_lean_ir_type2id___main(x_21);
x_23 = l_lean_ir_type2id___main(x_1);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
lean::dec(x_22);
if (x_24 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_0);
x_28 = l_lean_ir_match__type___closed__5;
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_3);
return x_29;
}
else
{
obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_30 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_31 = 0;
x_32 = l_lean_ir_check__ne__type___closed__1;
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_30);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_31);
x_34 = x_33;
x_35 = l_lean_ir_check__ne__type___closed__2;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_31);
x_37 = x_36;
x_38 = l_lean_ir_type_to__format___main(x_1);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_31);
x_40 = x_39;
x_41 = l_lean_ir_match__type___closed__3;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_31);
x_43 = x_42;
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_3);
return x_45;
}
}
}
}
obj* l_lean_ir_check__ne__type___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__ne__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_invalid__literal___rarg___closed__1() {
_start:
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
obj* l_lean_ir_invalid__literal___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_ir_invalid__literal___rarg___closed__1;
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_lean_ir_invalid__literal(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_invalid__literal___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_ir_literal_check(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_2);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_7; uint8 x_8; 
lean::dec(x_0);
x_6 = l_lean_ir_type2id___main(x_1);
x_7 = l_lean_ir_is__arith__ty___closed__1;
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
obj* x_10; obj* x_11; 
x_10 = l_lean_ir_invalid__literal___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_3);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
x_12 = l_lean_ir_match__type___closed__5;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
case 1:
{
obj* x_15; obj* x_16; uint8 x_17; 
lean::dec(x_0);
x_15 = l_lean_ir_type2id___main(x_1);
x_16 = l_lean_ir_valid__assign__unop__types___closed__1;
x_17 = lean::nat_dec_eq(x_15, x_16);
lean::dec(x_15);
if (x_17 == 0)
{
obj* x_19; obj* x_20; 
x_19 = l_lean_ir_invalid__literal___rarg___closed__1;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_3);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = l_lean_ir_match__type___closed__5;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_3);
return x_22;
}
}
case 2:
{
obj* x_23; uint8 x_26; obj* x_27; uint8 x_28; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = l_lean_ir_is__nonfloat__arith__ty(x_1);
x_27 = l_int_zero;
x_28 = lean::int_dec_lt(x_23, x_27);
lean::dec(x_23);
if (x_26 == 0)
{
obj* x_30; 
x_30 = l_lean_ir_invalid__literal___rarg___closed__1;
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_33 = x_30;
} else {
 lean::inc(x_31);
 lean::dec(x_30);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_3);
return x_35;
}
else
{
if (x_28 == 0)
{
obj* x_36; obj* x_37; 
x_36 = l_lean_ir_match__type___closed__5;
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_3);
return x_37;
}
else
{
uint8 x_38; 
x_38 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_38 == 0)
{
obj* x_39; 
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_30);
lean::cnstr_set(x_39, 1, x_3);
return x_39;
}
else
{
obj* x_40; obj* x_41; 
x_40 = l_lean_ir_match__type___closed__5;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_3);
return x_41;
}
}
}
}
else
{
if (x_28 == 0)
{
obj* x_42; obj* x_43; 
x_42 = l_lean_ir_match__type___closed__5;
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_3);
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_44 == 0)
{
obj* x_45; obj* x_46; 
x_45 = l_lean_ir_invalid__literal___rarg___closed__1;
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_3);
return x_46;
}
else
{
obj* x_47; obj* x_48; 
x_47 = l_lean_ir_match__type___closed__5;
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_3);
return x_48;
}
}
}
}
default:
{
obj* x_50; obj* x_51; uint8 x_52; 
lean::dec(x_0);
x_50 = l_lean_ir_type2id___main(x_1);
x_51 = l_lean_ir_is__nonfloat__arith__ty___closed__2;
x_52 = lean::nat_dec_eq(x_50, x_51);
if (x_52 == 0)
{
obj* x_53; uint8 x_54; 
x_53 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_54 = lean::nat_dec_eq(x_50, x_53);
lean::dec(x_50);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
x_56 = l_lean_ir_invalid__literal___rarg___closed__1;
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_3);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_lean_ir_match__type___closed__5;
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_3);
return x_59;
}
}
else
{
obj* x_61; obj* x_62; 
lean::dec(x_50);
x_61 = l_lean_ir_match__type___closed__5;
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_3);
return x_62;
}
}
}
}
}
obj* l_lean_ir_literal_check___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_literal_check(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_get__decl___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown function `");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_get__decl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_release(x_1, 1);
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
lean::inc(x_0);
x_7 = lean::apply_1(x_3, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_0);
x_9 = 0;
x_10 = l_lean_ir_get__decl___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l_lean_ir_match__type___closed__3;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
if (lean::is_scalar(x_5)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_5;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
if (lean::is_scalar(x_5)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_5;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
}
}
obj* l_lean_ir_set__result__types___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_set__result__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_instr_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; uint8 x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_8 = l_lean_ir_set__type(x_5, x_7, x_1, x_2);
x_3 = x_8;
goto lbl_4;
}
case 1:
{
obj* x_9; uint8 x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_12 = l_lean_ir_set__type(x_9, x_11, x_1, x_2);
x_3 = x_12;
goto lbl_4;
}
case 2:
{
obj* x_13; uint8 x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_16 = l_lean_ir_set__type(x_13, x_15, x_1, x_2);
x_3 = x_16;
goto lbl_4;
}
case 3:
{
obj* x_17; uint8 x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_20 = l_lean_ir_set__type(x_17, x_19, x_1, x_2);
x_3 = x_20;
goto lbl_4;
}
case 4:
{
obj* x_22; obj* x_23; 
lean::dec(x_1);
x_22 = l_lean_ir_match__type___closed__5;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_2);
x_3 = x_23;
goto lbl_4;
}
case 5:
{
obj* x_24; obj* x_26; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
lean::inc(x_1);
x_29 = l_lean_ir_get__decl(x_26, x_1, x_2);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
lean::dec(x_24);
x_34 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_36 = x_29;
} else {
 lean::inc(x_34);
 lean::dec(x_29);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_39 = x_30;
} else {
 lean::inc(x_37);
 lean::dec(x_30);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_34);
x_3 = x_41;
goto lbl_4;
}
else
{
obj* x_42; obj* x_45; obj* x_48; obj* x_49; uint8 x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_29, 1);
lean::inc(x_42);
lean::dec(x_29);
x_45 = lean::cnstr_get(x_30, 0);
lean::inc(x_45);
lean::dec(x_30);
x_48 = l_lean_ir_decl_header___main(x_45);
x_49 = lean::cnstr_get(x_48, 2);
lean::inc(x_49);
lean::dec(x_48);
x_52 = lean::unbox(x_49);
x_53 = l_lean_ir_set__type(x_24, x_52, x_1, x_42);
x_3 = x_53;
goto lbl_4;
}
}
case 7:
{
obj* x_55; obj* x_56; 
lean::dec(x_1);
x_55 = l_lean_ir_match__type___closed__5;
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_2);
x_3 = x_56;
goto lbl_4;
}
case 9:
{
obj* x_58; obj* x_59; 
lean::dec(x_1);
x_58 = l_lean_ir_match__type___closed__5;
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_2);
x_3 = x_59;
goto lbl_4;
}
case 10:
{
obj* x_60; uint8 x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_0, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_63 = l_lean_ir_set__type(x_60, x_62, x_1, x_2);
x_3 = x_63;
goto lbl_4;
}
case 15:
{
obj* x_65; obj* x_66; 
lean::dec(x_1);
x_65 = l_lean_ir_match__type___closed__5;
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_2);
x_3 = x_66;
goto lbl_4;
}
default:
{
obj* x_67; uint8 x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_0, 0);
lean::inc(x_67);
x_69 = 11;
x_70 = l_lean_ir_set__type(x_67, x_69, x_1, x_2);
x_3 = x_70;
goto lbl_4;
}
}
lbl_4:
{
obj* x_71; 
x_71 = lean::cnstr_get(x_3, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_73 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_75 = x_3;
} else {
 lean::inc(x_73);
 lean::dec(x_3);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_78 = x_71;
} else {
 lean::inc(x_76);
 lean::dec(x_71);
 x_78 = lean::box(0);
}
x_79 = l_lean_ir_instr_to__format___main(x_0);
x_80 = 0;
x_81 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_79);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_80);
x_83 = x_82;
x_84 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_80);
x_86 = x_85;
x_87 = lean::box(1);
x_88 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_87);
lean::cnstr_set_scalar(x_88, sizeof(void*)*2, x_80);
x_89 = x_88;
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_76);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_80);
x_91 = x_90;
if (lean::is_scalar(x_78)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_78;
}
lean::cnstr_set(x_92, 0, x_91);
if (lean::is_scalar(x_75)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_75;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_73);
return x_93;
}
else
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_0);
x_95 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_97 = x_3;
} else {
 lean::inc(x_95);
 lean::dec(x_3);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_71);
lean::cnstr_set(x_98, 1, x_95);
return x_98;
}
}
}
}
obj* l_lean_ir_phi_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = l_lean_ir_set__type(x_3, x_5, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
x_15 = l_lean_ir_phi_to__format___main(x_0);
x_16 = 0;
x_17 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_16);
x_19 = x_18;
x_20 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_16);
x_22 = x_21;
x_23 = lean::box(1);
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_16);
x_25 = x_24;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_16);
x_27 = x_26;
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_9);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_0);
x_31 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_33 = x_6;
} else {
 lean::inc(x_31);
 lean::dec(x_6);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
obj* l_lean_ir_arg_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::dec(x_0);
x_7 = l_lean_ir_set__type(x_3, x_5, x_1, x_2);
return x_7;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_phi_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_instr_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_block_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
x_6 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_16);
x_20 = 0;
x_21 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_20);
x_23 = x_22;
x_24 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_20);
x_26 = x_25;
x_27 = lean::box(1);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_20);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_13);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_20);
x_31 = x_30;
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_10);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_7);
x_35 = lean::cnstr_get(x_6, 1);
lean::inc(x_35);
lean::dec(x_6);
x_38 = lean::cnstr_get(x_0, 2);
lean::inc(x_38);
x_40 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(x_38, x_1, x_35);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_43 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_45 = x_40;
} else {
 lean::inc(x_43);
 lean::dec(x_40);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
lean::dec(x_0);
x_52 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_49);
x_53 = 0;
x_54 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_52);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_53);
x_56 = x_55;
x_57 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_53);
x_59 = x_58;
x_60 = lean::box(1);
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_53);
x_62 = x_61;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_46);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_53);
x_64 = x_63;
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
if (lean::is_scalar(x_45)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_45;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_43);
return x_66;
}
else
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_0);
x_68 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_70 = x_40;
} else {
 lean::inc(x_68);
 lean::dec(x_40);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_41);
lean::cnstr_set(x_71, 1, x_68);
return x_71;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_arg_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_block_infer__types(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_infer__types___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
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
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::inc(x_1);
x_16 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(x_13, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_10);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_23 = x_16;
} else {
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_26 = x_17;
} else {
 lean::inc(x_24);
 lean::dec(x_17);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
lean::dec(x_8);
x_30 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_27);
x_31 = 0;
x_32 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_30);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_31);
x_34 = x_33;
x_35 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_31);
x_37 = x_36;
x_38 = lean::box(1);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_31);
x_40 = x_39;
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_24);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_31);
x_42 = x_41;
if (lean::is_scalar(x_26)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_26;
}
lean::cnstr_set(x_43, 0, x_42);
if (lean::is_scalar(x_23)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_23;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_21);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_17);
x_46 = lean::cnstr_get(x_16, 1);
lean::inc(x_46);
lean::dec(x_16);
x_49 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(x_10, x_1, x_46);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_61; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_52 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 x_54 = x_49;
} else {
 lean::inc(x_52);
 lean::dec(x_49);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_57 = x_50;
} else {
 lean::inc(x_55);
 lean::dec(x_50);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_8, 0);
lean::inc(x_58);
lean::dec(x_8);
x_61 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_58);
x_62 = 0;
x_63 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_61);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_62);
x_65 = x_64;
x_66 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_66);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_62);
x_68 = x_67;
x_69 = lean::box(1);
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_62);
x_71 = x_70;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_55);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_62);
x_73 = x_72;
if (lean::is_scalar(x_57)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_57;
}
lean::cnstr_set(x_74, 0, x_73);
if (lean::is_scalar(x_54)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_54;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_52);
return x_75;
}
else
{
obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_8);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_77 = x_50;
} else {
 lean::dec(x_50);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 x_80 = x_49;
} else {
 lean::inc(x_78);
 lean::dec(x_49);
 x_80 = lean::box(0);
}
lean::inc(x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_78);
if (lean::is_scalar(x_80)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_80;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_78);
return x_83;
}
}
}
}
}
obj* l_lean_ir_decl_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_decl_infer__types___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_infer__types(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_8; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = l_lean_ir_decl_header___main(x_0);
x_5 = lean::cnstr_get(x_4, 2);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_ir_type__checker__m_run___rarg(x_3, x_1, x_5);
return x_8;
}
}
obj* _init_l_lean_ir_check__arg__types___main___closed__1() {
_start:
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
obj* l_lean_ir_check__arg__types___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_lean_ir_match__type___closed__5;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
else
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
x_8 = l_lean_ir_check__arg__types___main___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_0);
lean::dec(x_2);
x_12 = l_lean_ir_check__arg__types___main___closed__1;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_21; uint8 x_24; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
lean::dec(x_19);
lean::inc(x_2);
x_27 = l_lean_ir_check__type(x_14, x_24, x_2, x_3);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_2);
lean::dec(x_21);
lean::dec(x_16);
x_33 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_38 = x_28;
} else {
 lean::inc(x_36);
 lean::dec(x_28);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
if (lean::is_scalar(x_35)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_35;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_33);
return x_40;
}
else
{
obj* x_42; 
lean::dec(x_28);
x_42 = lean::cnstr_get(x_27, 1);
lean::inc(x_42);
lean::dec(x_27);
x_0 = x_16;
x_1 = x_21;
x_3 = x_42;
goto _start;
}
}
}
}
}
obj* l_lean_ir_check__arg__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_check__arg__types___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; uint8 x_11; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = 11;
lean::inc(x_1);
x_13 = l_lean_ir_check__type(x_6, x_11, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_20 = x_13;
} else {
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
else
{
obj* x_27; 
lean::dec(x_14);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
x_0 = x_8;
x_2 = x_27;
goto _start;
}
}
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1() {
_start:
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
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; uint8 x_11; obj* x_13; obj* x_14; uint8 x_15; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::dec(x_6);
x_13 = l_lean_ir_type2id___main(x_11);
x_14 = l_lean_ir_valid__assign__unop__types___closed__1;
x_15 = lean::nat_dec_eq(x_13, x_14);
lean::dec(x_13);
if (x_15 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_8);
lean::dec(x_1);
x_19 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
}
else
{
x_0 = x_8;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; uint8 x_11; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = 11;
lean::inc(x_1);
x_13 = l_lean_ir_check__type(x_6, x_11, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_20 = x_13;
} else {
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
else
{
obj* x_27; 
lean::dec(x_14);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
x_0 = x_8;
x_2 = x_27;
goto _start;
}
}
}
}
obj* _init_l_lean_ir_instr_check___closed__1() {
_start:
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
obj* _init_l_lean_ir_instr_check___closed__2() {
_start:
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
obj* _init_l_lean_ir_instr_check___closed__3() {
_start:
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
obj* _init_l_lean_ir_instr_check___closed__4() {
_start:
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
obj* _init_l_lean_ir_instr_check___closed__5() {
_start:
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
obj* l_lean_ir_instr_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_5; obj* x_6; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = l_lean_ir_get__type(x_6, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
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
obj* x_19; obj* x_21; obj* x_22; obj* x_25; uint8 x_26; obj* x_27; uint8 x_28; 
x_19 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_21 = x_8;
} else {
 lean::inc(x_19);
 lean::dec(x_8);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_9, 0);
lean::inc(x_22);
lean::dec(x_9);
x_25 = l_lean_ir_type2id___main(x_5);
x_26 = lean::unbox(x_22);
x_27 = l_lean_ir_type2id___main(x_26);
x_28 = lean::nat_dec_eq(x_25, x_27);
lean::dec(x_27);
lean::dec(x_25);
if (x_28 == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_lean_ir_instr_check___closed__1;
if (lean::is_scalar(x_21)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_21;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_19);
x_3 = x_32;
goto lbl_4;
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_21)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_21;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_19);
x_3 = x_34;
goto lbl_4;
}
}
}
case 1:
{
uint8 x_35; obj* x_36; obj* x_38; 
x_35 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_36 = lean::cnstr_get(x_0, 1);
lean::inc(x_36);
x_38 = l_lean_ir_literal_check(x_36, x_35, x_1, x_2);
x_3 = x_38;
goto lbl_4;
}
case 2:
{
uint8 x_39; uint8 x_40; obj* x_41; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_40 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_41 = lean::cnstr_get(x_0, 1);
lean::inc(x_41);
x_43 = l_lean_ir_get__type(x_41, x_1, x_2);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_48)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_48;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
x_3 = x_53;
goto lbl_4;
}
else
{
obj* x_54; obj* x_56; obj* x_57; uint8 x_60; uint8 x_61; 
x_54 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_set(x_43, 1, lean::box(0));
 x_56 = x_43;
} else {
 lean::inc(x_54);
 lean::dec(x_43);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_44, 0);
lean::inc(x_57);
lean::dec(x_44);
x_60 = lean::unbox(x_57);
x_61 = l_lean_ir_valid__assign__unop__types(x_40, x_39, x_60);
if (x_61 == 0)
{
obj* x_62; obj* x_63; 
x_62 = l_lean_ir_instr_check___closed__2;
if (lean::is_scalar(x_56)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_56;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_54);
x_3 = x_63;
goto lbl_4;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_56)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_56;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_54);
x_3 = x_65;
goto lbl_4;
}
}
}
case 3:
{
uint8 x_66; uint8 x_67; obj* x_68; obj* x_70; obj* x_73; obj* x_74; 
x_66 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_67 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_68 = lean::cnstr_get(x_0, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_0, 2);
lean::inc(x_70);
lean::inc(x_1);
x_73 = l_lean_ir_get__type(x_68, x_1, x_2);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_70);
x_78 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_80 = x_73;
} else {
 lean::inc(x_78);
 lean::dec(x_73);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_83 = x_74;
} else {
 lean::inc(x_81);
 lean::dec(x_74);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_80)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_80;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_78);
x_3 = x_85;
goto lbl_4;
}
else
{
obj* x_86; obj* x_89; obj* x_92; obj* x_93; 
x_86 = lean::cnstr_get(x_73, 1);
lean::inc(x_86);
lean::dec(x_73);
x_89 = lean::cnstr_get(x_74, 0);
lean::inc(x_89);
lean::dec(x_74);
x_92 = l_lean_ir_get__type(x_70, x_1, x_86);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_89);
x_96 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_98 = x_92;
} else {
 lean::inc(x_96);
 lean::dec(x_92);
 x_98 = lean::box(0);
}
x_99 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_101 = x_93;
} else {
 lean::inc(x_99);
 lean::dec(x_93);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
if (lean::is_scalar(x_98)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_98;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_96);
x_3 = x_103;
goto lbl_4;
}
else
{
obj* x_104; obj* x_106; obj* x_107; uint8 x_110; uint8 x_111; uint8 x_112; 
x_104 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_set(x_92, 1, lean::box(0));
 x_106 = x_92;
} else {
 lean::inc(x_104);
 lean::dec(x_92);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_93, 0);
lean::inc(x_107);
lean::dec(x_93);
x_110 = lean::unbox(x_89);
x_111 = lean::unbox(x_107);
x_112 = l_lean_ir_valid__assign__binop__types(x_67, x_66, x_110, x_111);
if (x_112 == 0)
{
obj* x_113; obj* x_114; 
x_113 = l_lean_ir_instr_check___closed__3;
if (lean::is_scalar(x_106)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_106;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_104);
x_3 = x_114;
goto lbl_4;
}
else
{
obj* x_115; obj* x_116; 
x_115 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_106)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_106;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_104);
x_3 = x_116;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_117; uint8 x_119; obj* x_120; 
x_117 = lean::cnstr_get(x_0, 0);
lean::inc(x_117);
x_119 = 11;
x_120 = l_lean_ir_check__type(x_117, x_119, x_1, x_2);
x_3 = x_120;
goto lbl_4;
}
case 5:
{
obj* x_121; obj* x_123; obj* x_126; obj* x_127; 
x_121 = lean::cnstr_get(x_0, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_0, 2);
lean::inc(x_123);
lean::inc(x_1);
x_126 = l_lean_ir_get__decl(x_121, x_1, x_2);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_123);
lean::dec(x_1);
x_131 = lean::cnstr_get(x_126, 1);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_133 = x_126;
} else {
 lean::inc(x_131);
 lean::dec(x_126);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_134);
if (lean::is_scalar(x_133)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_133;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_131);
x_3 = x_138;
goto lbl_4;
}
else
{
obj* x_139; obj* x_142; obj* x_145; obj* x_146; obj* x_149; 
x_139 = lean::cnstr_get(x_126, 1);
lean::inc(x_139);
lean::dec(x_126);
x_142 = lean::cnstr_get(x_127, 0);
lean::inc(x_142);
lean::dec(x_127);
x_145 = l_lean_ir_decl_header___main(x_142);
x_146 = lean::cnstr_get(x_145, 1);
lean::inc(x_146);
lean::dec(x_145);
x_149 = l_lean_ir_check__arg__types___main(x_123, x_146, x_1, x_139);
x_3 = x_149;
goto lbl_4;
}
}
case 6:
{
obj* x_151; obj* x_152; 
lean::dec(x_1);
x_151 = l_lean_ir_match__type___closed__5;
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_2);
x_3 = x_152;
goto lbl_4;
}
case 7:
{
obj* x_153; obj* x_155; uint8 x_157; obj* x_159; obj* x_160; 
x_153 = lean::cnstr_get(x_0, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_0, 1);
lean::inc(x_155);
x_157 = 11;
lean::inc(x_1);
x_159 = l_lean_ir_check__type(x_153, x_157, x_1, x_2);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
if (lean::obj_tag(x_160) == 0)
{
obj* x_164; obj* x_166; obj* x_167; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_1);
lean::dec(x_155);
x_164 = lean::cnstr_get(x_159, 1);
if (lean::is_exclusive(x_159)) {
 lean::cnstr_release(x_159, 0);
 x_166 = x_159;
} else {
 lean::inc(x_164);
 lean::dec(x_159);
 x_166 = lean::box(0);
}
x_167 = lean::cnstr_get(x_160, 0);
if (lean::is_exclusive(x_160)) {
 x_169 = x_160;
} else {
 lean::inc(x_167);
 lean::dec(x_160);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
if (lean::is_scalar(x_166)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_166;
}
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_164);
x_3 = x_171;
goto lbl_4;
}
else
{
obj* x_173; obj* x_176; 
lean::dec(x_160);
x_173 = lean::cnstr_get(x_159, 1);
lean::inc(x_173);
lean::dec(x_159);
x_176 = l_lean_ir_check__type(x_155, x_157, x_1, x_173);
x_3 = x_176;
goto lbl_4;
}
}
case 8:
{
obj* x_177; uint8 x_179; obj* x_180; 
x_177 = lean::cnstr_get(x_0, 1);
lean::inc(x_177);
x_179 = 11;
x_180 = l_lean_ir_check__type(x_177, x_179, x_1, x_2);
x_3 = x_180;
goto lbl_4;
}
case 9:
{
obj* x_181; obj* x_183; uint8 x_185; obj* x_187; obj* x_188; 
x_181 = lean::cnstr_get(x_0, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_0, 1);
lean::inc(x_183);
x_185 = 11;
lean::inc(x_1);
x_187 = l_lean_ir_check__type(x_181, x_185, x_1, x_2);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_183);
lean::dec(x_1);
x_192 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_194 = x_187;
} else {
 lean::inc(x_192);
 lean::dec(x_187);
 x_194 = lean::box(0);
}
x_195 = lean::cnstr_get(x_188, 0);
if (lean::is_exclusive(x_188)) {
 x_197 = x_188;
} else {
 lean::inc(x_195);
 lean::dec(x_188);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_195);
if (lean::is_scalar(x_194)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_194;
}
lean::cnstr_set(x_199, 0, x_198);
lean::cnstr_set(x_199, 1, x_192);
x_3 = x_199;
goto lbl_4;
}
else
{
obj* x_201; obj* x_204; 
lean::dec(x_188);
x_201 = lean::cnstr_get(x_187, 1);
lean::inc(x_201);
lean::dec(x_187);
x_204 = l_lean_ir_check__ne__type(x_183, x_185, x_1, x_201);
x_3 = x_204;
goto lbl_4;
}
}
case 10:
{
obj* x_205; obj* x_207; uint8 x_209; obj* x_211; obj* x_212; 
x_205 = lean::cnstr_get(x_0, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_0, 1);
lean::inc(x_207);
x_209 = 11;
lean::inc(x_1);
x_211 = l_lean_ir_check__type(x_207, x_209, x_1, x_2);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
if (lean::obj_tag(x_212) == 0)
{
obj* x_216; obj* x_218; obj* x_219; obj* x_221; obj* x_222; obj* x_223; 
lean::dec(x_1);
lean::dec(x_205);
x_216 = lean::cnstr_get(x_211, 1);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_218 = x_211;
} else {
 lean::inc(x_216);
 lean::dec(x_211);
 x_218 = lean::box(0);
}
x_219 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_221 = x_212;
} else {
 lean::inc(x_219);
 lean::dec(x_212);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_219);
if (lean::is_scalar(x_218)) {
 x_223 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_223 = x_218;
}
lean::cnstr_set(x_223, 0, x_222);
lean::cnstr_set(x_223, 1, x_216);
x_3 = x_223;
goto lbl_4;
}
else
{
obj* x_225; obj* x_228; 
lean::dec(x_212);
x_225 = lean::cnstr_get(x_211, 1);
lean::inc(x_225);
lean::dec(x_211);
x_228 = l_lean_ir_check__ne__type(x_205, x_209, x_1, x_225);
x_3 = x_228;
goto lbl_4;
}
}
case 11:
{
obj* x_229; obj* x_231; obj* x_235; obj* x_236; 
x_229 = lean::cnstr_get(x_0, 1);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_0, 2);
lean::inc(x_231);
lean::inc(x_1);
lean::inc(x_231);
x_235 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(x_231, x_1, x_2);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
if (lean::obj_tag(x_236) == 0)
{
obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_231);
lean::dec(x_1);
lean::dec(x_229);
x_241 = lean::cnstr_get(x_235, 1);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 x_243 = x_235;
} else {
 lean::inc(x_241);
 lean::dec(x_235);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_236, 0);
if (lean::is_exclusive(x_236)) {
 x_246 = x_236;
} else {
 lean::inc(x_244);
 lean::dec(x_236);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_244);
if (lean::is_scalar(x_243)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_243;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_241);
x_3 = x_248;
goto lbl_4;
}
else
{
obj* x_250; obj* x_254; obj* x_255; 
lean::dec(x_236);
x_250 = lean::cnstr_get(x_235, 1);
lean::inc(x_250);
lean::dec(x_235);
lean::inc(x_1);
x_254 = l_lean_ir_get__decl(x_229, x_1, x_250);
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
if (lean::obj_tag(x_255) == 0)
{
obj* x_259; obj* x_261; obj* x_262; obj* x_264; obj* x_265; obj* x_266; 
lean::dec(x_231);
lean::dec(x_1);
x_259 = lean::cnstr_get(x_254, 1);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 x_261 = x_254;
} else {
 lean::inc(x_259);
 lean::dec(x_254);
 x_261 = lean::box(0);
}
x_262 = lean::cnstr_get(x_255, 0);
if (lean::is_exclusive(x_255)) {
 x_264 = x_255;
} else {
 lean::inc(x_262);
 lean::dec(x_255);
 x_264 = lean::box(0);
}
if (lean::is_scalar(x_264)) {
 x_265 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_265 = x_264;
}
lean::cnstr_set(x_265, 0, x_262);
if (lean::is_scalar(x_261)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_261;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_259);
x_3 = x_266;
goto lbl_4;
}
else
{
obj* x_267; obj* x_269; obj* x_270; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_280; uint8 x_281; 
x_267 = lean::cnstr_get(x_254, 1);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 lean::cnstr_set(x_254, 1, lean::box(0));
 x_269 = x_254;
} else {
 lean::inc(x_267);
 lean::dec(x_254);
 x_269 = lean::box(0);
}
x_270 = lean::cnstr_get(x_255, 0);
lean::inc(x_270);
lean::dec(x_255);
x_273 = lean::mk_nat_obj(0u);
x_274 = l_list_length__aux___main___rarg(x_231, x_273);
x_275 = l_lean_ir_decl_header___main(x_270);
x_276 = lean::cnstr_get(x_275, 1);
lean::inc(x_276);
lean::dec(x_275);
lean::inc(x_276);
x_280 = l_list_length__aux___main___rarg(x_276, x_273);
x_281 = lean::nat_dec_le(x_274, x_280);
lean::dec(x_280);
lean::dec(x_274);
if (x_281 == 0)
{
obj* x_286; obj* x_287; 
lean::dec(x_1);
lean::dec(x_276);
x_286 = l_lean_ir_instr_check___closed__4;
if (lean::is_scalar(x_269)) {
 x_287 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_287 = x_269;
}
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_267);
x_3 = x_287;
goto lbl_4;
}
else
{
obj* x_289; 
lean::dec(x_269);
x_289 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(x_276, x_1, x_267);
x_3 = x_289;
goto lbl_4;
}
}
}
}
case 12:
{
obj* x_290; obj* x_292; 
x_290 = lean::cnstr_get(x_0, 1);
lean::inc(x_290);
x_292 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(x_290, x_1, x_2);
x_3 = x_292;
goto lbl_4;
}
case 13:
{
obj* x_293; obj* x_295; uint8 x_297; obj* x_299; obj* x_300; 
x_293 = lean::cnstr_get(x_0, 1);
lean::inc(x_293);
x_295 = lean::cnstr_get(x_0, 2);
lean::inc(x_295);
x_297 = 5;
lean::inc(x_1);
x_299 = l_lean_ir_check__type(x_293, x_297, x_1, x_2);
x_300 = lean::cnstr_get(x_299, 0);
lean::inc(x_300);
if (lean::obj_tag(x_300) == 0)
{
obj* x_304; obj* x_306; obj* x_307; obj* x_309; obj* x_310; obj* x_311; 
lean::dec(x_1);
lean::dec(x_295);
x_304 = lean::cnstr_get(x_299, 1);
if (lean::is_exclusive(x_299)) {
 lean::cnstr_release(x_299, 0);
 x_306 = x_299;
} else {
 lean::inc(x_304);
 lean::dec(x_299);
 x_306 = lean::box(0);
}
x_307 = lean::cnstr_get(x_300, 0);
if (lean::is_exclusive(x_300)) {
 x_309 = x_300;
} else {
 lean::inc(x_307);
 lean::dec(x_300);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_307);
if (lean::is_scalar(x_306)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_306;
}
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_304);
x_3 = x_311;
goto lbl_4;
}
else
{
obj* x_313; obj* x_316; 
lean::dec(x_300);
x_313 = lean::cnstr_get(x_299, 1);
lean::inc(x_313);
lean::dec(x_299);
x_316 = l_lean_ir_check__type(x_295, x_297, x_1, x_313);
x_3 = x_316;
goto lbl_4;
}
}
case 14:
{
uint8 x_317; obj* x_318; obj* x_320; obj* x_322; obj* x_323; uint8 x_324; 
x_317 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_318 = lean::cnstr_get(x_0, 1);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_0, 2);
lean::inc(x_320);
x_322 = l_lean_ir_type2id___main(x_317);
x_323 = l_lean_ir_valid__assign__unop__types___closed__1;
x_324 = lean::nat_dec_eq(x_322, x_323);
lean::dec(x_322);
if (x_324 == 0)
{
uint8 x_326; obj* x_328; obj* x_329; 
x_326 = 5;
lean::inc(x_1);
x_328 = l_lean_ir_check__type(x_318, x_326, x_1, x_2);
x_329 = lean::cnstr_get(x_328, 0);
lean::inc(x_329);
if (lean::obj_tag(x_329) == 0)
{
obj* x_333; obj* x_335; obj* x_336; obj* x_338; obj* x_339; obj* x_340; 
lean::dec(x_320);
lean::dec(x_1);
x_333 = lean::cnstr_get(x_328, 1);
if (lean::is_exclusive(x_328)) {
 lean::cnstr_release(x_328, 0);
 x_335 = x_328;
} else {
 lean::inc(x_333);
 lean::dec(x_328);
 x_335 = lean::box(0);
}
x_336 = lean::cnstr_get(x_329, 0);
if (lean::is_exclusive(x_329)) {
 x_338 = x_329;
} else {
 lean::inc(x_336);
 lean::dec(x_329);
 x_338 = lean::box(0);
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_336);
if (lean::is_scalar(x_335)) {
 x_340 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_340 = x_335;
}
lean::cnstr_set(x_340, 0, x_339);
lean::cnstr_set(x_340, 1, x_333);
x_3 = x_340;
goto lbl_4;
}
else
{
obj* x_342; obj* x_345; obj* x_346; 
lean::dec(x_329);
x_342 = lean::cnstr_get(x_328, 1);
lean::inc(x_342);
lean::dec(x_328);
x_345 = l_lean_ir_check__type(x_320, x_326, x_1, x_342);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
if (lean::obj_tag(x_346) == 0)
{
obj* x_348; obj* x_350; obj* x_351; obj* x_353; obj* x_354; obj* x_355; 
x_348 = lean::cnstr_get(x_345, 1);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 x_350 = x_345;
} else {
 lean::inc(x_348);
 lean::dec(x_345);
 x_350 = lean::box(0);
}
x_351 = lean::cnstr_get(x_346, 0);
if (lean::is_exclusive(x_346)) {
 x_353 = x_346;
} else {
 lean::inc(x_351);
 lean::dec(x_346);
 x_353 = lean::box(0);
}
if (lean::is_scalar(x_353)) {
 x_354 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_354 = x_353;
}
lean::cnstr_set(x_354, 0, x_351);
if (lean::is_scalar(x_350)) {
 x_355 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_355 = x_350;
}
lean::cnstr_set(x_355, 0, x_354);
lean::cnstr_set(x_355, 1, x_348);
x_3 = x_355;
goto lbl_4;
}
else
{
obj* x_357; obj* x_359; obj* x_360; obj* x_361; 
lean::dec(x_346);
x_357 = lean::cnstr_get(x_345, 1);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 x_359 = x_345;
} else {
 lean::inc(x_357);
 lean::dec(x_345);
 x_359 = lean::box(0);
}
x_360 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_359)) {
 x_361 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_361 = x_359;
}
lean::cnstr_set(x_361, 0, x_360);
lean::cnstr_set(x_361, 1, x_357);
x_3 = x_361;
goto lbl_4;
}
}
}
else
{
uint8 x_362; obj* x_364; obj* x_365; 
x_362 = 5;
lean::inc(x_1);
x_364 = l_lean_ir_check__type(x_318, x_362, x_1, x_2);
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
if (lean::obj_tag(x_365) == 0)
{
obj* x_369; obj* x_371; obj* x_372; obj* x_374; obj* x_375; obj* x_376; 
lean::dec(x_320);
lean::dec(x_1);
x_369 = lean::cnstr_get(x_364, 1);
if (lean::is_exclusive(x_364)) {
 lean::cnstr_release(x_364, 0);
 x_371 = x_364;
} else {
 lean::inc(x_369);
 lean::dec(x_364);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_365, 0);
if (lean::is_exclusive(x_365)) {
 x_374 = x_365;
} else {
 lean::inc(x_372);
 lean::dec(x_365);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_372);
if (lean::is_scalar(x_371)) {
 x_376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_376 = x_371;
}
lean::cnstr_set(x_376, 0, x_375);
lean::cnstr_set(x_376, 1, x_369);
x_3 = x_376;
goto lbl_4;
}
else
{
obj* x_378; obj* x_381; obj* x_382; 
lean::dec(x_365);
x_378 = lean::cnstr_get(x_364, 1);
lean::inc(x_378);
lean::dec(x_364);
x_381 = l_lean_ir_check__type(x_320, x_362, x_1, x_378);
x_382 = lean::cnstr_get(x_381, 0);
lean::inc(x_382);
if (lean::obj_tag(x_382) == 0)
{
obj* x_384; obj* x_386; obj* x_387; obj* x_389; obj* x_390; obj* x_391; 
x_384 = lean::cnstr_get(x_381, 1);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 x_386 = x_381;
} else {
 lean::inc(x_384);
 lean::dec(x_381);
 x_386 = lean::box(0);
}
x_387 = lean::cnstr_get(x_382, 0);
if (lean::is_exclusive(x_382)) {
 x_389 = x_382;
} else {
 lean::inc(x_387);
 lean::dec(x_382);
 x_389 = lean::box(0);
}
if (lean::is_scalar(x_389)) {
 x_390 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_390 = x_389;
}
lean::cnstr_set(x_390, 0, x_387);
if (lean::is_scalar(x_386)) {
 x_391 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_391 = x_386;
}
lean::cnstr_set(x_391, 0, x_390);
lean::cnstr_set(x_391, 1, x_384);
x_3 = x_391;
goto lbl_4;
}
else
{
obj* x_393; obj* x_395; obj* x_396; obj* x_397; 
lean::dec(x_382);
x_393 = lean::cnstr_get(x_381, 1);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 x_395 = x_381;
} else {
 lean::inc(x_393);
 lean::dec(x_381);
 x_395 = lean::box(0);
}
x_396 = l_lean_ir_instr_check___closed__5;
if (lean::is_scalar(x_395)) {
 x_397 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_397 = x_395;
}
lean::cnstr_set(x_397, 0, x_396);
lean::cnstr_set(x_397, 1, x_393);
x_3 = x_397;
goto lbl_4;
}
}
}
}
default:
{
obj* x_398; obj* x_400; uint8 x_402; obj* x_404; obj* x_405; 
x_398 = lean::cnstr_get(x_0, 0);
lean::inc(x_398);
x_400 = lean::cnstr_get(x_0, 1);
lean::inc(x_400);
x_402 = 11;
lean::inc(x_1);
x_404 = l_lean_ir_check__type(x_398, x_402, x_1, x_2);
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
if (lean::obj_tag(x_405) == 0)
{
obj* x_409; obj* x_411; obj* x_412; obj* x_414; obj* x_415; obj* x_416; 
lean::dec(x_400);
lean::dec(x_1);
x_409 = lean::cnstr_get(x_404, 1);
if (lean::is_exclusive(x_404)) {
 lean::cnstr_release(x_404, 0);
 x_411 = x_404;
} else {
 lean::inc(x_409);
 lean::dec(x_404);
 x_411 = lean::box(0);
}
x_412 = lean::cnstr_get(x_405, 0);
if (lean::is_exclusive(x_405)) {
 x_414 = x_405;
} else {
 lean::inc(x_412);
 lean::dec(x_405);
 x_414 = lean::box(0);
}
if (lean::is_scalar(x_414)) {
 x_415 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_415 = x_414;
}
lean::cnstr_set(x_415, 0, x_412);
if (lean::is_scalar(x_411)) {
 x_416 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_416 = x_411;
}
lean::cnstr_set(x_416, 0, x_415);
lean::cnstr_set(x_416, 1, x_409);
x_3 = x_416;
goto lbl_4;
}
else
{
obj* x_418; uint8 x_421; obj* x_422; 
lean::dec(x_405);
x_418 = lean::cnstr_get(x_404, 1);
lean::inc(x_418);
lean::dec(x_404);
x_421 = 5;
x_422 = l_lean_ir_check__type(x_400, x_421, x_1, x_418);
x_3 = x_422;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_423; 
x_423 = lean::cnstr_get(x_3, 0);
lean::inc(x_423);
if (lean::obj_tag(x_423) == 0)
{
obj* x_425; obj* x_427; obj* x_428; obj* x_430; obj* x_431; uint8 x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
x_425 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_427 = x_3;
} else {
 lean::inc(x_425);
 lean::dec(x_3);
 x_427 = lean::box(0);
}
x_428 = lean::cnstr_get(x_423, 0);
if (lean::is_exclusive(x_423)) {
 x_430 = x_423;
} else {
 lean::inc(x_428);
 lean::dec(x_423);
 x_430 = lean::box(0);
}
x_431 = l_lean_ir_instr_to__format___main(x_0);
x_432 = 0;
x_433 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_434 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_434, 0, x_433);
lean::cnstr_set(x_434, 1, x_431);
lean::cnstr_set_scalar(x_434, sizeof(void*)*2, x_432);
x_435 = x_434;
x_436 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_437 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_437, 0, x_435);
lean::cnstr_set(x_437, 1, x_436);
lean::cnstr_set_scalar(x_437, sizeof(void*)*2, x_432);
x_438 = x_437;
x_439 = lean::box(1);
x_440 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_440, 0, x_438);
lean::cnstr_set(x_440, 1, x_439);
lean::cnstr_set_scalar(x_440, sizeof(void*)*2, x_432);
x_441 = x_440;
x_442 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_442, 0, x_441);
lean::cnstr_set(x_442, 1, x_428);
lean::cnstr_set_scalar(x_442, sizeof(void*)*2, x_432);
x_443 = x_442;
if (lean::is_scalar(x_430)) {
 x_444 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_444 = x_430;
}
lean::cnstr_set(x_444, 0, x_443);
if (lean::is_scalar(x_427)) {
 x_445 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_445 = x_427;
}
lean::cnstr_set(x_445, 0, x_444);
lean::cnstr_set(x_445, 1, x_425);
return x_445;
}
else
{
obj* x_447; obj* x_449; obj* x_450; 
lean::dec(x_0);
x_447 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_449 = x_3;
} else {
 lean::inc(x_447);
 lean::dec(x_3);
 x_449 = lean::box(0);
}
if (lean::is_scalar(x_449)) {
 x_450 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_450 = x_449;
}
lean::cnstr_set(x_450, 0, x_423);
lean::cnstr_set(x_450, 1, x_447);
return x_450;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_lean_ir_match__type___closed__5;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_10; uint8 x_13; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
lean::inc(x_2);
x_15 = l_lean_ir_check__type(x_8, x_13, x_2, x_3);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_23 = x_15;
} else {
 lean::inc(x_21);
 lean::dec(x_15);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_26 = x_16;
} else {
 lean::inc(x_24);
 lean::dec(x_16);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_23)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_23;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
return x_28;
}
else
{
obj* x_30; 
lean::dec(x_16);
x_30 = lean::cnstr_get(x_15, 1);
lean::inc(x_30);
lean::dec(x_15);
x_1 = x_10;
x_3 = x_30;
goto _start;
}
}
}
}
obj* l_lean_ir_phi_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_0);
x_6 = l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(x_0, x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
x_15 = l_lean_ir_phi_to__format___main(x_0);
x_16 = 0;
x_17 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_16);
x_19 = x_18;
x_20 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_16);
x_22 = x_21;
x_23 = lean::box(1);
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_16);
x_25 = x_24;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_16);
x_27 = x_26;
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_9);
return x_29;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_0);
x_31 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_33 = x_6;
} else {
 lean::inc(x_31);
 lean::dec(x_6);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_7);
lean::cnstr_set(x_34, 1, x_31);
return x_34;
}
}
}
obj* l_lean_ir_check__result__type___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_check__result__type(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_terminator_check___closed__1() {
_start:
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
obj* l_lean_ir_terminator_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; uint8 x_10; obj* x_11; obj* x_12; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::unbox(x_8);
x_11 = l_lean_ir_check__type(x_6, x_10, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_3 = x_12;
x_4 = x_14;
goto lbl_5;
}
case 1:
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = l_lean_ir_get__type(x_17, x_1, x_2);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_25; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_27 = x_20;
} else {
 lean::inc(x_25);
 lean::dec(x_20);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
x_3 = x_28;
x_4 = x_22;
goto lbl_5;
}
else
{
obj* x_29; obj* x_32; uint8 x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_29 = lean::cnstr_get(x_19, 1);
lean::inc(x_29);
lean::dec(x_19);
x_32 = lean::cnstr_get(x_20, 0);
lean::inc(x_32);
lean::dec(x_20);
x_35 = lean::unbox(x_32);
x_36 = l_lean_ir_type2id___main(x_35);
x_37 = l_lean_ir_is__arith__ty___closed__1;
x_38 = lean::nat_dec_eq(x_36, x_37);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
x_39 = l_lean_ir_valid__assign__unop__types___closed__3;
x_40 = lean::nat_dec_eq(x_36, x_39);
lean::dec(x_36);
if (x_40 == 0)
{
obj* x_42; 
x_42 = l_lean_ir_terminator_check___closed__1;
x_3 = x_42;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_43; 
x_43 = l_lean_ir_match__type___closed__5;
x_3 = x_43;
x_4 = x_29;
goto lbl_5;
}
}
else
{
obj* x_45; 
lean::dec(x_36);
x_45 = l_lean_ir_match__type___closed__5;
x_3 = x_45;
x_4 = x_29;
goto lbl_5;
}
}
}
default:
{
obj* x_47; 
lean::dec(x_1);
x_47 = l_lean_ir_match__type___closed__5;
x_3 = x_47;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_48; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_48 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_50 = x_3;
} else {
 lean::inc(x_48);
 lean::dec(x_3);
 x_50 = lean::box(0);
}
x_51 = l_lean_ir_terminator_to__format___main(x_0);
x_52 = 0;
x_53 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_52);
x_55 = x_54;
x_56 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_52);
x_58 = x_57;
x_59 = lean::box(1);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_52);
x_61 = x_60;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_48);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_52);
x_63 = x_62;
if (lean::is_scalar(x_50)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_50;
}
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_4);
return x_65;
}
else
{
obj* x_67; 
lean::dec(x_0);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_3);
lean::cnstr_set(x_67, 1, x_4);
return x_67;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_phi_check(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_instr_check(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_block_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
lean::inc(x_1);
x_11 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(x_3, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
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
obj* x_22; obj* x_25; obj* x_28; obj* x_29; obj* x_31; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::cnstr_get(x_0, 2);
lean::inc(x_25);
lean::inc(x_1);
x_28 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(x_25, x_1, x_22);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_7 = x_29;
x_8 = x_31;
goto lbl_9;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_42; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_5);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_38 = x_7;
} else {
 lean::inc(x_36);
 lean::dec(x_7);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
lean::dec(x_0);
x_42 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_39);
x_43 = 0;
x_44 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_42);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_43);
x_46 = x_45;
x_47 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_43);
x_49 = x_48;
x_50 = lean::box(1);
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_43);
x_52 = x_51;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_36);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_43);
x_54 = x_53;
if (lean::is_scalar(x_38)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_38;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_8);
return x_56;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_7);
x_58 = l_lean_ir_terminator_check(x_5, x_1, x_8);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_61 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_63 = x_58;
} else {
 lean::inc(x_61);
 lean::dec(x_58);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_66 = x_59;
} else {
 lean::inc(x_64);
 lean::dec(x_59);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_0, 0);
lean::inc(x_67);
lean::dec(x_0);
x_70 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_67);
x_71 = 0;
x_72 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_70);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_71);
x_74 = x_73;
x_75 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_71);
x_77 = x_76;
x_78 = lean::box(1);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_71);
x_80 = x_79;
x_81 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_64);
lean::cnstr_set_scalar(x_81, sizeof(void*)*2, x_71);
x_82 = x_81;
if (lean::is_scalar(x_66)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_66;
}
lean::cnstr_set(x_83, 0, x_82);
if (lean::is_scalar(x_63)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_63;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_61);
return x_84;
}
else
{
obj* x_86; obj* x_88; obj* x_89; 
lean::dec(x_0);
x_86 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_88 = x_58;
} else {
 lean::inc(x_86);
 lean::dec(x_58);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_59);
lean::cnstr_set(x_89, 1, x_86);
return x_89;
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_block_check(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_check___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(x_7, x_1, x_2);
return x_10;
}
}
}
obj* l_lean_ir_decl_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_decl_check___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
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
obj* l_except__t_bind__cont___at_lean_ir_type__check___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
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
obj* l_reader__t_bind___at_lean_ir_type__check___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_ir_type__check___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_lean_ir_decl_check___main(x_0, x_2, x_3);
return x_5;
}
}
obj* l_lean_ir_type__check___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
}
obj* _init_l_lean_ir_type__check___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__check___lambda__2), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_type__check(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; 
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_infer__types), 3, 1);
lean::closure_set(x_3, 0, x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type__check___lambda__1), 4, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_type__check___spec__1___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_6);
x_8 = l_lean_ir_type__check___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = l_lean_ir_decl_header___main(x_0);
x_11 = lean::cnstr_get(x_10, 2);
lean::inc(x_11);
lean::dec(x_10);
x_14 = l_lean_ir_type__checker__m_run___rarg(x_9, x_1, x_11);
return x_14;
}
}
void initialize_init_lean_ir_instances();
void initialize_init_lean_ir_format();
void initialize_init_control_combinators();
static bool _G_initialized = false;
void initialize_init_lean_ir_type__check() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_instances();
 initialize_init_lean_ir_format();
 initialize_init_control_combinators();
 l_lean_ir_is__arith__ty___closed__1 = _init_l_lean_ir_is__arith__ty___closed__1();
lean::mark_persistent(l_lean_ir_is__arith__ty___closed__1);
 l_lean_ir_is__nonfloat__arith__ty___closed__1 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__1();
lean::mark_persistent(l_lean_ir_is__nonfloat__arith__ty___closed__1);
 l_lean_ir_is__nonfloat__arith__ty___closed__2 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__2();
lean::mark_persistent(l_lean_ir_is__nonfloat__arith__ty___closed__2);
 l_lean_ir_valid__assign__unop__types___closed__1 = _init_l_lean_ir_valid__assign__unop__types___closed__1();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__1);
 l_lean_ir_valid__assign__unop__types___closed__2 = _init_l_lean_ir_valid__assign__unop__types___closed__2();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__2);
 l_lean_ir_valid__assign__unop__types___closed__3 = _init_l_lean_ir_valid__assign__unop__types___closed__3();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__3);
 l_lean_ir_valid__assign__unop__types___closed__4 = _init_l_lean_ir_valid__assign__unop__types___closed__4();
lean::mark_persistent(l_lean_ir_valid__assign__unop__types___closed__4);
 l_lean_ir_type__checker__m = _init_l_lean_ir_type__checker__m();
lean::mark_persistent(l_lean_ir_type__checker__m);
 l_lean_ir_match__type___closed__1 = _init_l_lean_ir_match__type___closed__1();
lean::mark_persistent(l_lean_ir_match__type___closed__1);
 l_lean_ir_match__type___closed__2 = _init_l_lean_ir_match__type___closed__2();
lean::mark_persistent(l_lean_ir_match__type___closed__2);
 l_lean_ir_match__type___closed__3 = _init_l_lean_ir_match__type___closed__3();
lean::mark_persistent(l_lean_ir_match__type___closed__3);
 l_lean_ir_match__type___closed__4 = _init_l_lean_ir_match__type___closed__4();
lean::mark_persistent(l_lean_ir_match__type___closed__4);
 l_lean_ir_match__type___closed__5 = _init_l_lean_ir_match__type___closed__5();
lean::mark_persistent(l_lean_ir_match__type___closed__5);
 l_lean_ir_get__type___closed__1 = _init_l_lean_ir_get__type___closed__1();
lean::mark_persistent(l_lean_ir_get__type___closed__1);
 l_lean_ir_check__type___closed__1 = _init_l_lean_ir_check__type___closed__1();
lean::mark_persistent(l_lean_ir_check__type___closed__1);
 l_lean_ir_check__type___closed__2 = _init_l_lean_ir_check__type___closed__2();
lean::mark_persistent(l_lean_ir_check__type___closed__2);
 l_lean_ir_check__ne__type___closed__1 = _init_l_lean_ir_check__ne__type___closed__1();
lean::mark_persistent(l_lean_ir_check__ne__type___closed__1);
 l_lean_ir_check__ne__type___closed__2 = _init_l_lean_ir_check__ne__type___closed__2();
lean::mark_persistent(l_lean_ir_check__ne__type___closed__2);
 l_lean_ir_invalid__literal___rarg___closed__1 = _init_l_lean_ir_invalid__literal___rarg___closed__1();
lean::mark_persistent(l_lean_ir_invalid__literal___rarg___closed__1);
 l_lean_ir_get__decl___closed__1 = _init_l_lean_ir_get__decl___closed__1();
lean::mark_persistent(l_lean_ir_get__decl___closed__1);
 l_lean_ir_check__arg__types___main___closed__1 = _init_l_lean_ir_check__arg__types___main___closed__1();
lean::mark_persistent(l_lean_ir_check__arg__types___main___closed__1);
 l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1);
 l_lean_ir_instr_check___closed__1 = _init_l_lean_ir_instr_check___closed__1();
lean::mark_persistent(l_lean_ir_instr_check___closed__1);
 l_lean_ir_instr_check___closed__2 = _init_l_lean_ir_instr_check___closed__2();
lean::mark_persistent(l_lean_ir_instr_check___closed__2);
 l_lean_ir_instr_check___closed__3 = _init_l_lean_ir_instr_check___closed__3();
lean::mark_persistent(l_lean_ir_instr_check___closed__3);
 l_lean_ir_instr_check___closed__4 = _init_l_lean_ir_instr_check___closed__4();
lean::mark_persistent(l_lean_ir_instr_check___closed__4);
 l_lean_ir_instr_check___closed__5 = _init_l_lean_ir_instr_check___closed__5();
lean::mark_persistent(l_lean_ir_instr_check___closed__5);
 l_lean_ir_terminator_check___closed__1 = _init_l_lean_ir_terminator_check___closed__1();
lean::mark_persistent(l_lean_ir_terminator_check___closed__1);
 l_lean_ir_type__check___closed__1 = _init_l_lean_ir_type__check___closed__1();
lean::mark_persistent(l_lean_ir_type__check___closed__1);
}
