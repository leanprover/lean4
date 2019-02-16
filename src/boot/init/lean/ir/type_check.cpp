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
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
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
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
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
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_set__type___spec__1___boxed(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
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
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__context;
obj* l_lean_ir_literal_check(obj*, uint8, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
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
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_type__checker__m_run___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = l_lean_ir_mk__context;
lean::inc(x_4);
x_6 = lean::apply_2(x_0, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
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
obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_11 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_12 = 0;
x_13 = l_lean_ir_match__type___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_11);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_12);
x_16 = x_15;
x_17 = l_lean_ir_match__type___closed__2;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_12);
x_20 = x_19;
x_21 = l_lean_ir_type_to__format___main(x_1);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_12);
x_23 = x_22;
x_24 = l_lean_ir_match__type___closed__3;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_12);
x_27 = x_26;
x_28 = l_lean_ir_match__type___closed__4;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_12);
x_31 = x_30;
x_32 = l_lean_ir_type_to__format___main(x_2);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_12);
x_34 = x_33;
lean::inc(x_24);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_24);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_12);
x_37 = x_36;
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_4);
return x_39;
}
else
{
obj* x_41; obj* x_43; 
lean::dec(x_0);
x_41 = l_lean_ir_match__type___closed__5;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_4);
return x_43;
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
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
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
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_11);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
lean::dec(x_9);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; uint8 x_45; 
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
x_44 = l_lean_name_quick__lt___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; uint8 x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = l_lean_name_quick__lt___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_1);
lean::dec(x_39);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
lean::dec(x_37);
x_0 = x_39;
goto _start;
}
}
else
{
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_33;
goto _start;
}
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
obj* x_8; uint8 x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_6);
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_9 = 0;
x_10 = l_lean_ir_get__type___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_9);
x_13 = x_12;
x_14 = l_lean_ir_match__type___closed__3;
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
obj* l_rbnode_ins___main___at_lean_ir_set__type___spec__3(obj* x_0, obj* x_1, uint8 x_2) {
_start:
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
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; uint8 x_18; 
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
x_17 = l_lean_name_quick__lt___main(x_1, x_8);
x_18 = lean::unbox(x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_22; uint8 x_23; 
lean::inc(x_1);
lean::inc(x_8);
x_22 = l_lean_name_quick__lt___main(x_8, x_1);
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
x_29 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_12, x_1, x_2);
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
x_31 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_6, x_1, x_2);
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
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
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
x_44 = l_lean_name_quick__lt___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; uint8 x_50; 
lean::inc(x_1);
lean::inc(x_35);
x_49 = l_lean_name_quick__lt___main(x_35, x_1);
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
uint8 x_57; 
lean::inc(x_39);
x_57 = l_rbnode_get__color___main___rarg(x_39);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_41);
x_59 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_39, x_1, x_2);
x_60 = l_rbnode_balance2__node___main___rarg(x_59, x_35, x_37, x_33);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_39, x_1, x_2);
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
uint8 x_64; 
lean::inc(x_33);
x_64 = l_rbnode_get__color___main___rarg(x_33);
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_41);
x_66 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_33, x_1, x_2);
x_67 = l_rbnode_balance1__node___main___rarg(x_66, x_35, x_37, x_39);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_33, x_1, x_2);
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
obj* l_rbnode_insert___at_lean_ir_set__type___spec__2(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_set__type___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
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
obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_6);
lean::dec(x_2);
x_9 = l_rbnode_insert___at_lean_ir_set__type___spec__2(x_3, x_0, x_1);
x_10 = l_lean_ir_match__type___closed__5;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; uint8 x_16; obj* x_18; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::unbox(x_13);
lean::dec(x_13);
x_18 = l_lean_ir_match__type(x_0, x_16, x_1, x_2, x_3);
return x_18;
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
obj* x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_2);
x_9 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_10 = 0;
x_11 = l_lean_ir_check__type___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = l_lean_ir_check__type___closed__2;
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
obj* x_21; uint8 x_24; obj* x_26; 
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
x_24 = lean::unbox(x_21);
lean::dec(x_21);
x_26 = l_lean_ir_match__type(x_0, x_24, x_1, x_2, x_3);
return x_26;
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
obj* x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_9 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_10 = 0;
x_11 = l_lean_ir_check__type___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = l_lean_ir_check__type___closed__2;
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
obj* x_21; uint8 x_24; obj* x_26; obj* x_27; uint8 x_28; 
x_21 = lean::cnstr_get(x_7, 0);
lean::inc(x_21);
lean::dec(x_7);
x_24 = lean::unbox(x_21);
lean::dec(x_21);
x_26 = l_lean_ir_type2id___main(x_24);
x_27 = l_lean_ir_type2id___main(x_1);
x_28 = lean::nat_dec_eq(x_26, x_27);
lean::dec(x_27);
lean::dec(x_26);
if (x_28 == 0)
{
obj* x_32; obj* x_34; 
lean::dec(x_0);
x_32 = l_lean_ir_match__type___closed__5;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_3);
return x_34;
}
else
{
obj* x_35; uint8 x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_35 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_36 = 0;
x_37 = l_lean_ir_check__ne__type___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_36);
x_40 = x_39;
x_41 = l_lean_ir_check__ne__type___closed__2;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_36);
x_44 = x_43;
x_45 = l_lean_ir_type_to__format___main(x_1);
x_46 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*2, x_36);
x_47 = x_46;
x_48 = l_lean_ir_match__type___closed__3;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_47);
lean::cnstr_set(x_50, 1, x_48);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_36);
x_51 = x_50;
x_52 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_3);
return x_53;
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
obj* x_1; obj* x_3; 
x_1 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
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
obj* x_10; obj* x_12; 
x_10 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
else
{
obj* x_13; obj* x_15; 
x_13 = l_lean_ir_match__type___closed__5;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_3);
return x_15;
}
}
case 1:
{
obj* x_17; obj* x_18; uint8 x_19; 
lean::dec(x_0);
x_17 = l_lean_ir_type2id___main(x_1);
x_18 = l_lean_ir_valid__assign__unop__types___closed__1;
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_17);
if (x_19 == 0)
{
obj* x_21; obj* x_23; 
x_21 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_3);
return x_23;
}
else
{
obj* x_24; obj* x_26; 
x_24 = l_lean_ir_match__type___closed__5;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_3);
return x_26;
}
}
case 2:
{
obj* x_27; uint8 x_30; obj* x_31; uint8 x_32; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
x_30 = l_lean_ir_is__nonfloat__arith__ty(x_1);
x_31 = l_int_zero;
x_32 = lean::int_dec_lt(x_27, x_31);
lean::dec(x_27);
if (x_30 == 0)
{
obj* x_34; 
x_34 = l_lean_ir_invalid__literal___rarg___closed__1;
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
lean::inc(x_34);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 x_38 = x_34;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_3);
return x_40;
}
else
{
if (x_32 == 0)
{
obj* x_41; obj* x_43; 
x_41 = l_lean_ir_match__type___closed__5;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_3);
return x_43;
}
else
{
uint8 x_44; 
x_44 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_44 == 0)
{
obj* x_46; 
lean::inc(x_34);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_34);
lean::cnstr_set(x_46, 1, x_3);
return x_46;
}
else
{
obj* x_47; obj* x_49; 
x_47 = l_lean_ir_match__type___closed__5;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_3);
return x_49;
}
}
}
}
else
{
if (x_32 == 0)
{
obj* x_50; obj* x_52; 
x_50 = l_lean_ir_match__type___closed__5;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_3);
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_lean_ir_is__signed__arith__ty(x_1);
if (x_53 == 0)
{
obj* x_54; obj* x_56; 
x_54 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_3);
return x_56;
}
else
{
obj* x_57; obj* x_59; 
x_57 = l_lean_ir_match__type___closed__5;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_3);
return x_59;
}
}
}
}
default:
{
obj* x_61; obj* x_62; uint8 x_63; 
lean::dec(x_0);
x_61 = l_lean_ir_type2id___main(x_1);
x_62 = l_lean_ir_is__nonfloat__arith__ty___closed__2;
x_63 = lean::nat_dec_eq(x_61, x_62);
if (x_63 == 0)
{
obj* x_64; uint8 x_65; 
x_64 = l_lean_ir_is__nonfloat__arith__ty___closed__1;
x_65 = lean::nat_dec_eq(x_61, x_64);
lean::dec(x_61);
if (x_65 == 0)
{
obj* x_67; obj* x_69; 
x_67 = l_lean_ir_invalid__literal___rarg___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_3);
return x_69;
}
else
{
obj* x_70; obj* x_72; 
x_70 = l_lean_ir_match__type___closed__5;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_3);
return x_72;
}
}
else
{
obj* x_74; obj* x_76; 
lean::dec(x_61);
x_74 = l_lean_ir_match__type___closed__5;
lean::inc(x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_3);
return x_76;
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
obj* x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_9 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_0);
x_10 = 0;
x_11 = l_lean_ir_get__decl___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_10);
x_14 = x_13;
x_15 = l_lean_ir_match__type___closed__3;
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
obj* l_lean_ir_set__result__types___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* l_lean_ir_set__result__types(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_lean_ir_set__type(x_0, x_4, x_2, x_3);
return x_6;
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
obj* x_22; obj* x_24; 
lean::dec(x_1);
x_22 = l_lean_ir_match__type___closed__5;
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
x_30 = l_lean_ir_get__decl(x_27, x_1, x_2);
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
obj* x_44; obj* x_47; obj* x_48; uint8 x_51; obj* x_53; 
lean::dec(x_35);
x_44 = lean::cnstr_get(x_31, 0);
lean::inc(x_44);
lean::dec(x_31);
x_47 = l_lean_ir_decl_header___main(x_44);
x_48 = lean::cnstr_get(x_47, 2);
lean::inc(x_48);
lean::dec(x_47);
x_51 = lean::unbox(x_48);
lean::dec(x_48);
x_53 = l_lean_ir_set__type(x_25, x_51, x_1, x_33);
x_3 = x_53;
goto lbl_4;
}
}
case 7:
{
obj* x_55; obj* x_57; 
lean::dec(x_1);
x_55 = l_lean_ir_match__type___closed__5;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_2);
x_3 = x_57;
goto lbl_4;
}
case 9:
{
obj* x_59; obj* x_61; 
lean::dec(x_1);
x_59 = l_lean_ir_match__type___closed__5;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_2);
x_3 = x_61;
goto lbl_4;
}
case 10:
{
obj* x_62; uint8 x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_0, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_65 = l_lean_ir_set__type(x_62, x_64, x_1, x_2);
x_3 = x_65;
goto lbl_4;
}
case 15:
{
obj* x_67; obj* x_69; 
lean::dec(x_1);
x_67 = l_lean_ir_match__type___closed__5;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_2);
x_3 = x_69;
goto lbl_4;
}
default:
{
obj* x_70; uint8 x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_0, 0);
lean::inc(x_70);
x_72 = 11;
x_73 = l_lean_ir_set__type(x_70, x_72, x_1, x_2);
x_3 = x_73;
goto lbl_4;
}
}
lbl_4:
{
obj* x_74; obj* x_76; obj* x_78; 
x_74 = lean::cnstr_get(x_3, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_3, 1);
lean::inc(x_76);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_78 = x_3;
}
if (lean::obj_tag(x_74) == 0)
{
obj* x_79; obj* x_81; obj* x_82; uint8 x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_79 = lean::cnstr_get(x_74, 0);
lean::inc(x_79);
if (lean::is_shared(x_74)) {
 lean::dec(x_74);
 x_81 = lean::box(0);
} else {
 lean::cnstr_release(x_74, 0);
 x_81 = x_74;
}
x_82 = l_lean_ir_instr_to__format___main(x_0);
x_83 = 0;
x_84 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*2, x_83);
x_87 = x_86;
x_88 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_88);
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_88);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_83);
x_91 = x_90;
x_92 = lean::box(1);
x_93 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_92);
lean::cnstr_set_scalar(x_93, sizeof(void*)*2, x_83);
x_94 = x_93;
x_95 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_79);
lean::cnstr_set_scalar(x_95, sizeof(void*)*2, x_83);
x_96 = x_95;
if (lean::is_scalar(x_81)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_81;
}
lean::cnstr_set(x_97, 0, x_96);
if (lean::is_scalar(x_78)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_78;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_76);
return x_98;
}
else
{
obj* x_100; 
lean::dec(x_0);
if (lean::is_scalar(x_78)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_78;
}
lean::cnstr_set(x_100, 0, x_74);
lean::cnstr_set(x_100, 1, x_76);
return x_100;
}
}
}
}
obj* l_lean_ir_phi_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = l_lean_ir_set__type(x_3, x_5, x_1, x_2);
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
obj* x_12; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
}
x_15 = l_lean_ir_phi_to__format___main(x_0);
x_16 = 0;
x_17 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_16);
x_20 = x_19;
x_21 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_16);
x_24 = x_23;
x_25 = lean::box(1);
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_phi_infer__types(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_instr_infer__types(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_block_infer__types(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
x_6 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__1(x_3, x_1, x_2);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_19; uint8 x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
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
x_19 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_16);
x_20 = 0;
x_21 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_20);
x_24 = x_23;
x_25 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_20);
x_28 = x_27;
x_29 = lean::box(1);
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
x_39 = l_list_mmap_x_27___main___at_lean_ir_block_infer__types___spec__2(x_37, x_1, x_9);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_45; obj* x_48; obj* x_51; uint8 x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
lean::dec(x_0);
x_51 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_48);
x_52 = 0;
x_53 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_53);
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_52);
x_56 = x_55;
x_57 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_52);
x_60 = x_59;
x_61 = lean::box(1);
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
 lean::cnstr_set_tag(x_36, 0);
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
lean::dec(x_0);
lean::dec(x_36);
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
obj* l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_arg_infer__types(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_block_infer__types(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
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
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; 
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
obj* x_24; obj* x_26; obj* x_27; obj* x_30; uint8 x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
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
x_30 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_27);
x_31 = 0;
x_32 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_31);
x_35 = x_34;
x_36 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_36);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_31);
x_39 = x_38;
x_40 = lean::box(1);
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
x_48 = l_list_mmap_x_27___main___at_lean_ir_decl_infer__types___main___spec__2(x_10, x_1, x_19);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_54; obj* x_57; obj* x_60; uint8 x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_54 = lean::cnstr_get(x_49, 0);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::cnstr_get(x_8, 0);
lean::inc(x_57);
lean::dec(x_8);
x_60 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_57);
x_61 = 0;
x_62 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_61);
x_65 = x_64;
x_66 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_66);
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_66);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_61);
x_69 = x_68;
x_70 = lean::box(1);
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
 lean::cnstr_set_tag(x_47, 0);
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
lean::dec(x_8);
lean::dec(x_49);
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
lean::dec(x_0);
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
x_7 = l_lean_ir_match__type___closed__5;
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
x_11 = l_lean_ir_check__arg__types___main___closed__1;
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
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_2);
x_23 = l_lean_ir_check__arg__types___main___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_3);
return x_25;
}
else
{
obj* x_26; obj* x_28; uint8 x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_1, 1);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
lean::dec(x_26);
lean::inc(x_2);
x_34 = l_lean_ir_check__type(x_14, x_31, x_2, x_3);
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
lean::dec(x_39);
lean::dec(x_35);
x_0 = x_16;
x_1 = x_28;
x_3 = x_37;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; uint8 x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = 11;
lean::inc(x_1);
x_15 = l_lean_ir_check__type(x_8, x_13, x_1, x_2);
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
lean::dec(x_16);
lean::dec(x_20);
x_0 = x_10;
x_2 = x_18;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; uint8 x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::dec(x_8);
x_15 = l_lean_ir_type2id___main(x_13);
x_16 = l_lean_ir_valid__assign__unop__types___closed__1;
x_17 = lean::nat_dec_eq(x_15, x_16);
lean::dec(x_15);
if (x_17 == 0)
{
obj* x_21; obj* x_23; 
lean::dec(x_10);
lean::dec(x_1);
x_21 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
else
{
x_0 = x_10;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; uint8 x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = 11;
lean::inc(x_1);
x_15 = l_lean_ir_check__type(x_8, x_13, x_1, x_2);
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
lean::dec(x_16);
lean::dec(x_20);
x_0 = x_10;
x_2 = x_18;
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
uint8 x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = l_lean_ir_get__type(x_6, x_1, x_2);
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
obj* x_19; obj* x_22; uint8 x_23; obj* x_25; uint8 x_26; 
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
x_22 = l_lean_ir_type2id___main(x_5);
x_23 = lean::unbox(x_19);
lean::dec(x_19);
x_25 = l_lean_ir_type2id___main(x_23);
x_26 = lean::nat_dec_eq(x_22, x_25);
lean::dec(x_25);
lean::dec(x_22);
if (x_26 == 0)
{
obj* x_29; obj* x_31; 
x_29 = l_lean_ir_instr_check___closed__1;
lean::inc(x_29);
if (lean::is_scalar(x_13)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_13;
}
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_11);
x_3 = x_31;
goto lbl_4;
}
else
{
obj* x_32; obj* x_34; 
x_32 = l_lean_ir_match__type___closed__5;
lean::inc(x_32);
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_11);
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
uint8 x_39; uint8 x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; 
x_39 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_40 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_41 = lean::cnstr_get(x_0, 1);
lean::inc(x_41);
x_43 = l_lean_ir_get__type(x_41, x_1, x_2);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_48 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_48 = x_43;
}
if (lean::obj_tag(x_44) == 0)
{
obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
if (lean::is_shared(x_44)) {
 lean::dec(x_44);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_44, 0);
 x_51 = x_44;
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
obj* x_54; uint8 x_57; uint8 x_59; 
x_54 = lean::cnstr_get(x_44, 0);
lean::inc(x_54);
lean::dec(x_44);
x_57 = lean::unbox(x_54);
lean::dec(x_54);
x_59 = l_lean_ir_valid__assign__unop__types(x_40, x_39, x_57);
if (x_59 == 0)
{
obj* x_60; obj* x_62; 
x_60 = l_lean_ir_instr_check___closed__2;
lean::inc(x_60);
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_46);
x_3 = x_62;
goto lbl_4;
}
else
{
obj* x_63; obj* x_65; 
x_63 = l_lean_ir_match__type___closed__5;
lean::inc(x_63);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_46);
x_3 = x_65;
goto lbl_4;
}
}
}
case 3:
{
uint8 x_66; uint8 x_67; obj* x_68; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_78; 
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
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_78 = x_73;
}
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_70);
x_81 = lean::cnstr_get(x_74, 0);
lean::inc(x_81);
if (lean::is_shared(x_74)) {
 lean::dec(x_74);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_74, 0);
 x_83 = x_74;
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_78)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_78;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_76);
x_3 = x_85;
goto lbl_4;
}
else
{
obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_92; 
x_86 = lean::cnstr_get(x_74, 0);
lean::inc(x_86);
if (lean::is_shared(x_74)) {
 lean::dec(x_74);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_74, 0);
 x_88 = x_74;
}
x_89 = l_lean_ir_get__type(x_70, x_1, x_76);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_96; obj* x_99; obj* x_100; 
lean::dec(x_86);
x_96 = lean::cnstr_get(x_90, 0);
lean::inc(x_96);
lean::dec(x_90);
if (lean::is_scalar(x_88)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_88;
 lean::cnstr_set_tag(x_88, 0);
}
lean::cnstr_set(x_99, 0, x_96);
if (lean::is_scalar(x_78)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_78;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_92);
x_3 = x_100;
goto lbl_4;
}
else
{
obj* x_102; uint8 x_105; uint8 x_107; uint8 x_109; 
lean::dec(x_88);
x_102 = lean::cnstr_get(x_90, 0);
lean::inc(x_102);
lean::dec(x_90);
x_105 = lean::unbox(x_86);
lean::dec(x_86);
x_107 = lean::unbox(x_102);
lean::dec(x_102);
x_109 = l_lean_ir_valid__assign__binop__types(x_67, x_66, x_105, x_107);
if (x_109 == 0)
{
obj* x_110; obj* x_112; 
x_110 = l_lean_ir_instr_check___closed__3;
lean::inc(x_110);
if (lean::is_scalar(x_78)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_78;
}
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_92);
x_3 = x_112;
goto lbl_4;
}
else
{
obj* x_113; obj* x_115; 
x_113 = l_lean_ir_match__type___closed__5;
lean::inc(x_113);
if (lean::is_scalar(x_78)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_78;
}
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_92);
x_3 = x_115;
goto lbl_4;
}
}
}
}
case 4:
{
obj* x_116; uint8 x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_0, 0);
lean::inc(x_116);
x_118 = 11;
x_119 = l_lean_ir_check__type(x_116, x_118, x_1, x_2);
x_3 = x_119;
goto lbl_4;
}
case 5:
{
obj* x_120; obj* x_122; obj* x_125; obj* x_126; obj* x_128; obj* x_130; 
x_120 = lean::cnstr_get(x_0, 1);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_0, 2);
lean::inc(x_122);
lean::inc(x_1);
x_125 = l_lean_ir_get__decl(x_120, x_1, x_2);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
if (lean::is_shared(x_125)) {
 lean::dec(x_125);
 x_130 = lean::box(0);
} else {
 lean::cnstr_release(x_125, 0);
 lean::cnstr_release(x_125, 1);
 x_130 = x_125;
}
if (lean::obj_tag(x_126) == 0)
{
obj* x_133; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_1);
lean::dec(x_122);
x_133 = lean::cnstr_get(x_126, 0);
lean::inc(x_133);
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_135 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_135 = x_126;
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
if (lean::is_scalar(x_130)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_130;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_128);
x_3 = x_137;
goto lbl_4;
}
else
{
obj* x_139; obj* x_142; obj* x_143; obj* x_146; 
lean::dec(x_130);
x_139 = lean::cnstr_get(x_126, 0);
lean::inc(x_139);
lean::dec(x_126);
x_142 = l_lean_ir_decl_header___main(x_139);
x_143 = lean::cnstr_get(x_142, 1);
lean::inc(x_143);
lean::dec(x_142);
x_146 = l_lean_ir_check__arg__types___main(x_122, x_143, x_1, x_128);
x_3 = x_146;
goto lbl_4;
}
}
case 6:
{
obj* x_148; obj* x_150; 
lean::dec(x_1);
x_148 = l_lean_ir_match__type___closed__5;
lean::inc(x_148);
x_150 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_150, 0, x_148);
lean::cnstr_set(x_150, 1, x_2);
x_3 = x_150;
goto lbl_4;
}
case 7:
{
obj* x_151; obj* x_153; uint8 x_155; obj* x_157; obj* x_158; obj* x_160; obj* x_162; 
x_151 = lean::cnstr_get(x_0, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_0, 1);
lean::inc(x_153);
x_155 = 11;
lean::inc(x_1);
x_157 = l_lean_ir_check__type(x_151, x_155, x_1, x_2);
x_158 = lean::cnstr_get(x_157, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_157, 1);
lean::inc(x_160);
if (lean::is_shared(x_157)) {
 lean::dec(x_157);
 x_162 = lean::box(0);
} else {
 lean::cnstr_release(x_157, 0);
 lean::cnstr_release(x_157, 1);
 x_162 = x_157;
}
if (lean::obj_tag(x_158) == 0)
{
obj* x_165; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_1);
lean::dec(x_153);
x_165 = lean::cnstr_get(x_158, 0);
lean::inc(x_165);
if (lean::is_shared(x_158)) {
 lean::dec(x_158);
 x_167 = lean::box(0);
} else {
 lean::cnstr_release(x_158, 0);
 x_167 = x_158;
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
if (lean::is_scalar(x_162)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_162;
}
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_160);
x_3 = x_169;
goto lbl_4;
}
else
{
obj* x_172; 
lean::dec(x_162);
lean::dec(x_158);
x_172 = l_lean_ir_check__type(x_153, x_155, x_1, x_160);
x_3 = x_172;
goto lbl_4;
}
}
case 8:
{
obj* x_173; uint8 x_175; obj* x_176; 
x_173 = lean::cnstr_get(x_0, 1);
lean::inc(x_173);
x_175 = 11;
x_176 = l_lean_ir_check__type(x_173, x_175, x_1, x_2);
x_3 = x_176;
goto lbl_4;
}
case 9:
{
obj* x_177; obj* x_179; uint8 x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_188; 
x_177 = lean::cnstr_get(x_0, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_0, 1);
lean::inc(x_179);
x_181 = 11;
lean::inc(x_1);
x_183 = l_lean_ir_check__type(x_177, x_181, x_1, x_2);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
if (lean::is_shared(x_183)) {
 lean::dec(x_183);
 x_188 = lean::box(0);
} else {
 lean::cnstr_release(x_183, 0);
 lean::cnstr_release(x_183, 1);
 x_188 = x_183;
}
if (lean::obj_tag(x_184) == 0)
{
obj* x_191; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_179);
lean::dec(x_1);
x_191 = lean::cnstr_get(x_184, 0);
lean::inc(x_191);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_193 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 x_193 = x_184;
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_191);
if (lean::is_scalar(x_188)) {
 x_195 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_195 = x_188;
}
lean::cnstr_set(x_195, 0, x_194);
lean::cnstr_set(x_195, 1, x_186);
x_3 = x_195;
goto lbl_4;
}
else
{
obj* x_198; 
lean::dec(x_184);
lean::dec(x_188);
x_198 = l_lean_ir_check__ne__type(x_179, x_181, x_1, x_186);
x_3 = x_198;
goto lbl_4;
}
}
case 10:
{
obj* x_199; obj* x_201; uint8 x_203; obj* x_205; obj* x_206; obj* x_208; obj* x_210; 
x_199 = lean::cnstr_get(x_0, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_0, 1);
lean::inc(x_201);
x_203 = 11;
lean::inc(x_1);
x_205 = l_lean_ir_check__type(x_201, x_203, x_1, x_2);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
if (lean::is_shared(x_205)) {
 lean::dec(x_205);
 x_210 = lean::box(0);
} else {
 lean::cnstr_release(x_205, 0);
 lean::cnstr_release(x_205, 1);
 x_210 = x_205;
}
if (lean::obj_tag(x_206) == 0)
{
obj* x_213; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_199);
lean::dec(x_1);
x_213 = lean::cnstr_get(x_206, 0);
lean::inc(x_213);
if (lean::is_shared(x_206)) {
 lean::dec(x_206);
 x_215 = lean::box(0);
} else {
 lean::cnstr_release(x_206, 0);
 x_215 = x_206;
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
if (lean::is_scalar(x_210)) {
 x_217 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_217 = x_210;
}
lean::cnstr_set(x_217, 0, x_216);
lean::cnstr_set(x_217, 1, x_208);
x_3 = x_217;
goto lbl_4;
}
else
{
obj* x_220; 
lean::dec(x_210);
lean::dec(x_206);
x_220 = l_lean_ir_check__ne__type(x_199, x_203, x_1, x_208);
x_3 = x_220;
goto lbl_4;
}
}
case 11:
{
obj* x_221; obj* x_223; obj* x_227; obj* x_228; obj* x_230; obj* x_232; 
x_221 = lean::cnstr_get(x_0, 1);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_0, 2);
lean::inc(x_223);
lean::inc(x_1);
lean::inc(x_223);
x_227 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__1(x_223, x_1, x_2);
x_228 = lean::cnstr_get(x_227, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_227, 1);
lean::inc(x_230);
if (lean::is_shared(x_227)) {
 lean::dec(x_227);
 x_232 = lean::box(0);
} else {
 lean::cnstr_release(x_227, 0);
 lean::cnstr_release(x_227, 1);
 x_232 = x_227;
}
if (lean::obj_tag(x_228) == 0)
{
obj* x_236; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_221);
lean::dec(x_223);
lean::dec(x_1);
x_236 = lean::cnstr_get(x_228, 0);
lean::inc(x_236);
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_238 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_238 = x_228;
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
if (lean::is_scalar(x_232)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_232;
}
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_230);
x_3 = x_240;
goto lbl_4;
}
else
{
obj* x_241; obj* x_243; obj* x_244; obj* x_246; 
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_241 = x_228;
}
lean::inc(x_1);
x_243 = l_lean_ir_get__decl(x_221, x_1, x_230);
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get(x_243, 1);
lean::inc(x_246);
lean::dec(x_243);
if (lean::obj_tag(x_244) == 0)
{
obj* x_251; obj* x_254; obj* x_255; 
lean::dec(x_223);
lean::dec(x_1);
x_251 = lean::cnstr_get(x_244, 0);
lean::inc(x_251);
lean::dec(x_244);
if (lean::is_scalar(x_241)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_241;
 lean::cnstr_set_tag(x_241, 0);
}
lean::cnstr_set(x_254, 0, x_251);
if (lean::is_scalar(x_232)) {
 x_255 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_255 = x_232;
}
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_246);
x_3 = x_255;
goto lbl_4;
}
else
{
obj* x_257; obj* x_260; obj* x_262; obj* x_263; obj* x_264; obj* x_268; uint8 x_269; 
lean::dec(x_241);
x_257 = lean::cnstr_get(x_244, 0);
lean::inc(x_257);
lean::dec(x_244);
x_260 = lean::mk_nat_obj(0u);
lean::inc(x_260);
x_262 = l_list_length__aux___main___rarg(x_223, x_260);
x_263 = l_lean_ir_decl_header___main(x_257);
x_264 = lean::cnstr_get(x_263, 1);
lean::inc(x_264);
lean::dec(x_263);
lean::inc(x_264);
x_268 = l_list_length__aux___main___rarg(x_264, x_260);
x_269 = lean::nat_dec_le(x_262, x_268);
lean::dec(x_268);
lean::dec(x_262);
if (x_269 == 0)
{
obj* x_274; obj* x_276; 
lean::dec(x_1);
lean::dec(x_264);
x_274 = l_lean_ir_instr_check___closed__4;
lean::inc(x_274);
if (lean::is_scalar(x_232)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_232;
}
lean::cnstr_set(x_276, 0, x_274);
lean::cnstr_set(x_276, 1, x_246);
x_3 = x_276;
goto lbl_4;
}
else
{
obj* x_278; 
lean::dec(x_232);
x_278 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2(x_264, x_1, x_246);
x_3 = x_278;
goto lbl_4;
}
}
}
}
case 12:
{
obj* x_279; obj* x_281; 
x_279 = lean::cnstr_get(x_0, 1);
lean::inc(x_279);
x_281 = l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__3(x_279, x_1, x_2);
x_3 = x_281;
goto lbl_4;
}
case 13:
{
obj* x_282; obj* x_284; uint8 x_286; obj* x_288; obj* x_289; obj* x_291; obj* x_293; 
x_282 = lean::cnstr_get(x_0, 1);
lean::inc(x_282);
x_284 = lean::cnstr_get(x_0, 2);
lean::inc(x_284);
x_286 = 5;
lean::inc(x_1);
x_288 = l_lean_ir_check__type(x_282, x_286, x_1, x_2);
x_289 = lean::cnstr_get(x_288, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_288, 1);
lean::inc(x_291);
if (lean::is_shared(x_288)) {
 lean::dec(x_288);
 x_293 = lean::box(0);
} else {
 lean::cnstr_release(x_288, 0);
 lean::cnstr_release(x_288, 1);
 x_293 = x_288;
}
if (lean::obj_tag(x_289) == 0)
{
obj* x_296; obj* x_298; obj* x_299; obj* x_300; 
lean::dec(x_284);
lean::dec(x_1);
x_296 = lean::cnstr_get(x_289, 0);
lean::inc(x_296);
if (lean::is_shared(x_289)) {
 lean::dec(x_289);
 x_298 = lean::box(0);
} else {
 lean::cnstr_release(x_289, 0);
 x_298 = x_289;
}
if (lean::is_scalar(x_298)) {
 x_299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_299 = x_298;
}
lean::cnstr_set(x_299, 0, x_296);
if (lean::is_scalar(x_293)) {
 x_300 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_300 = x_293;
}
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_291);
x_3 = x_300;
goto lbl_4;
}
else
{
obj* x_303; 
lean::dec(x_293);
lean::dec(x_289);
x_303 = l_lean_ir_check__type(x_284, x_286, x_1, x_291);
x_3 = x_303;
goto lbl_4;
}
}
case 14:
{
uint8 x_304; obj* x_305; obj* x_307; obj* x_309; obj* x_310; uint8 x_311; 
x_304 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_305 = lean::cnstr_get(x_0, 1);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_0, 2);
lean::inc(x_307);
x_309 = l_lean_ir_type2id___main(x_304);
x_310 = l_lean_ir_valid__assign__unop__types___closed__1;
x_311 = lean::nat_dec_eq(x_309, x_310);
lean::dec(x_309);
if (x_311 == 0)
{
uint8 x_313; obj* x_315; obj* x_316; obj* x_318; obj* x_320; 
x_313 = 5;
lean::inc(x_1);
x_315 = l_lean_ir_check__type(x_305, x_313, x_1, x_2);
x_316 = lean::cnstr_get(x_315, 0);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_315, 1);
lean::inc(x_318);
if (lean::is_shared(x_315)) {
 lean::dec(x_315);
 x_320 = lean::box(0);
} else {
 lean::cnstr_release(x_315, 0);
 lean::cnstr_release(x_315, 1);
 x_320 = x_315;
}
if (lean::obj_tag(x_316) == 0)
{
obj* x_323; obj* x_325; obj* x_326; obj* x_327; 
lean::dec(x_1);
lean::dec(x_307);
x_323 = lean::cnstr_get(x_316, 0);
lean::inc(x_323);
if (lean::is_shared(x_316)) {
 lean::dec(x_316);
 x_325 = lean::box(0);
} else {
 lean::cnstr_release(x_316, 0);
 x_325 = x_316;
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_323);
if (lean::is_scalar(x_320)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_320;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_318);
x_3 = x_327;
goto lbl_4;
}
else
{
obj* x_328; obj* x_329; obj* x_330; obj* x_332; 
if (lean::is_shared(x_316)) {
 lean::dec(x_316);
 x_328 = lean::box(0);
} else {
 lean::cnstr_release(x_316, 0);
 x_328 = x_316;
}
x_329 = l_lean_ir_check__type(x_307, x_313, x_1, x_318);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
lean::dec(x_329);
if (lean::obj_tag(x_330) == 0)
{
obj* x_335; obj* x_338; obj* x_339; 
x_335 = lean::cnstr_get(x_330, 0);
lean::inc(x_335);
lean::dec(x_330);
if (lean::is_scalar(x_328)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_328;
 lean::cnstr_set_tag(x_328, 0);
}
lean::cnstr_set(x_338, 0, x_335);
if (lean::is_scalar(x_320)) {
 x_339 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_339 = x_320;
}
lean::cnstr_set(x_339, 0, x_338);
lean::cnstr_set(x_339, 1, x_332);
x_3 = x_339;
goto lbl_4;
}
else
{
obj* x_342; obj* x_344; 
lean::dec(x_328);
lean::dec(x_330);
x_342 = l_lean_ir_match__type___closed__5;
lean::inc(x_342);
if (lean::is_scalar(x_320)) {
 x_344 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_344 = x_320;
}
lean::cnstr_set(x_344, 0, x_342);
lean::cnstr_set(x_344, 1, x_332);
x_3 = x_344;
goto lbl_4;
}
}
}
else
{
uint8 x_345; obj* x_347; obj* x_348; obj* x_350; obj* x_352; 
x_345 = 5;
lean::inc(x_1);
x_347 = l_lean_ir_check__type(x_305, x_345, x_1, x_2);
x_348 = lean::cnstr_get(x_347, 0);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_347, 1);
lean::inc(x_350);
if (lean::is_shared(x_347)) {
 lean::dec(x_347);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_347, 0);
 lean::cnstr_release(x_347, 1);
 x_352 = x_347;
}
if (lean::obj_tag(x_348) == 0)
{
obj* x_355; obj* x_357; obj* x_358; obj* x_359; 
lean::dec(x_1);
lean::dec(x_307);
x_355 = lean::cnstr_get(x_348, 0);
lean::inc(x_355);
if (lean::is_shared(x_348)) {
 lean::dec(x_348);
 x_357 = lean::box(0);
} else {
 lean::cnstr_release(x_348, 0);
 x_357 = x_348;
}
if (lean::is_scalar(x_357)) {
 x_358 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_358 = x_357;
}
lean::cnstr_set(x_358, 0, x_355);
if (lean::is_scalar(x_352)) {
 x_359 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_359 = x_352;
}
lean::cnstr_set(x_359, 0, x_358);
lean::cnstr_set(x_359, 1, x_350);
x_3 = x_359;
goto lbl_4;
}
else
{
obj* x_360; obj* x_361; obj* x_362; obj* x_364; 
if (lean::is_shared(x_348)) {
 lean::dec(x_348);
 x_360 = lean::box(0);
} else {
 lean::cnstr_release(x_348, 0);
 x_360 = x_348;
}
x_361 = l_lean_ir_check__type(x_307, x_345, x_1, x_350);
x_362 = lean::cnstr_get(x_361, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_361, 1);
lean::inc(x_364);
lean::dec(x_361);
if (lean::obj_tag(x_362) == 0)
{
obj* x_367; obj* x_370; obj* x_371; 
x_367 = lean::cnstr_get(x_362, 0);
lean::inc(x_367);
lean::dec(x_362);
if (lean::is_scalar(x_360)) {
 x_370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_370 = x_360;
 lean::cnstr_set_tag(x_360, 0);
}
lean::cnstr_set(x_370, 0, x_367);
if (lean::is_scalar(x_352)) {
 x_371 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_371 = x_352;
}
lean::cnstr_set(x_371, 0, x_370);
lean::cnstr_set(x_371, 1, x_364);
x_3 = x_371;
goto lbl_4;
}
else
{
obj* x_374; obj* x_376; 
lean::dec(x_362);
lean::dec(x_360);
x_374 = l_lean_ir_instr_check___closed__5;
lean::inc(x_374);
if (lean::is_scalar(x_352)) {
 x_376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_376 = x_352;
}
lean::cnstr_set(x_376, 0, x_374);
lean::cnstr_set(x_376, 1, x_364);
x_3 = x_376;
goto lbl_4;
}
}
}
}
default:
{
obj* x_377; obj* x_379; uint8 x_381; obj* x_383; obj* x_384; obj* x_386; obj* x_388; 
x_377 = lean::cnstr_get(x_0, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_0, 1);
lean::inc(x_379);
x_381 = 11;
lean::inc(x_1);
x_383 = l_lean_ir_check__type(x_377, x_381, x_1, x_2);
x_384 = lean::cnstr_get(x_383, 0);
lean::inc(x_384);
x_386 = lean::cnstr_get(x_383, 1);
lean::inc(x_386);
if (lean::is_shared(x_383)) {
 lean::dec(x_383);
 x_388 = lean::box(0);
} else {
 lean::cnstr_release(x_383, 0);
 lean::cnstr_release(x_383, 1);
 x_388 = x_383;
}
if (lean::obj_tag(x_384) == 0)
{
obj* x_391; obj* x_393; obj* x_394; obj* x_395; 
lean::dec(x_1);
lean::dec(x_379);
x_391 = lean::cnstr_get(x_384, 0);
lean::inc(x_391);
if (lean::is_shared(x_384)) {
 lean::dec(x_384);
 x_393 = lean::box(0);
} else {
 lean::cnstr_release(x_384, 0);
 x_393 = x_384;
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_391);
if (lean::is_scalar(x_388)) {
 x_395 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_395 = x_388;
}
lean::cnstr_set(x_395, 0, x_394);
lean::cnstr_set(x_395, 1, x_386);
x_3 = x_395;
goto lbl_4;
}
else
{
uint8 x_398; obj* x_399; 
lean::dec(x_384);
lean::dec(x_388);
x_398 = 5;
x_399 = l_lean_ir_check__type(x_379, x_398, x_1, x_386);
x_3 = x_399;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_400; obj* x_402; obj* x_404; 
x_400 = lean::cnstr_get(x_3, 0);
lean::inc(x_400);
x_402 = lean::cnstr_get(x_3, 1);
lean::inc(x_402);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_404 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_404 = x_3;
}
if (lean::obj_tag(x_400) == 0)
{
obj* x_405; obj* x_407; obj* x_408; uint8 x_409; obj* x_410; obj* x_412; obj* x_413; obj* x_414; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; 
x_405 = lean::cnstr_get(x_400, 0);
lean::inc(x_405);
if (lean::is_shared(x_400)) {
 lean::dec(x_400);
 x_407 = lean::box(0);
} else {
 lean::cnstr_release(x_400, 0);
 x_407 = x_400;
}
x_408 = l_lean_ir_instr_to__format___main(x_0);
x_409 = 0;
x_410 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_410);
x_412 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_412, 0, x_410);
lean::cnstr_set(x_412, 1, x_408);
lean::cnstr_set_scalar(x_412, sizeof(void*)*2, x_409);
x_413 = x_412;
x_414 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_414);
x_416 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_416, 0, x_413);
lean::cnstr_set(x_416, 1, x_414);
lean::cnstr_set_scalar(x_416, sizeof(void*)*2, x_409);
x_417 = x_416;
x_418 = lean::box(1);
x_419 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_419, 0, x_417);
lean::cnstr_set(x_419, 1, x_418);
lean::cnstr_set_scalar(x_419, sizeof(void*)*2, x_409);
x_420 = x_419;
x_421 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_421, 0, x_420);
lean::cnstr_set(x_421, 1, x_405);
lean::cnstr_set_scalar(x_421, sizeof(void*)*2, x_409);
x_422 = x_421;
if (lean::is_scalar(x_407)) {
 x_423 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_423 = x_407;
}
lean::cnstr_set(x_423, 0, x_422);
if (lean::is_scalar(x_404)) {
 x_424 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_424 = x_404;
}
lean::cnstr_set(x_424, 0, x_423);
lean::cnstr_set(x_424, 1, x_402);
return x_424;
}
else
{
obj* x_426; 
lean::dec(x_0);
if (lean::is_scalar(x_404)) {
 x_426 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_426 = x_404;
}
lean::cnstr_set(x_426, 0, x_400);
lean::cnstr_set(x_426, 1, x_402);
return x_426;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = l_lean_ir_match__type___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; uint8 x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
lean::inc(x_2);
x_17 = l_lean_ir_check__type(x_10, x_15, x_2, x_3);
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
lean::dec(x_18);
lean::dec(x_22);
x_1 = x_12;
x_3 = x_20;
goto _start;
}
}
}
}
obj* l_lean_ir_phi_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_0);
x_6 = l_list_mmap_x_27___main___at_lean_ir_phi_check___spec__1(x_0, x_3, x_1, x_2);
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
obj* x_12; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
}
x_15 = l_lean_ir_phi_to__format___main(x_0);
x_16 = 0;
x_17 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_16);
x_20 = x_19;
x_21 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_16);
x_24 = x_23;
x_25 = lean::box(1);
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
obj* l_lean_ir_check__result__type___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_6;
}
}
obj* l_lean_ir_check__result__type(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_6; 
x_4 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_lean_ir_check__type(x_0, x_4, x_2, x_3);
return x_6;
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
obj* x_6; obj* x_8; uint8 x_10; obj* x_12; obj* x_13; obj* x_15; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::unbox(x_8);
lean::dec(x_8);
x_12 = l_lean_ir_check__type(x_6, x_10, x_1, x_2);
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
x_20 = l_lean_ir_get__type(x_18, x_1, x_2);
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
obj* x_30; uint8 x_33; obj* x_35; obj* x_36; uint8 x_37; 
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
lean::dec(x_21);
x_33 = lean::unbox(x_30);
lean::dec(x_30);
x_35 = l_lean_ir_type2id___main(x_33);
x_36 = l_lean_ir_is__arith__ty___closed__1;
x_37 = lean::nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = l_lean_ir_valid__assign__unop__types___closed__3;
x_39 = lean::nat_dec_eq(x_35, x_38);
lean::dec(x_35);
if (x_39 == 0)
{
obj* x_41; 
x_41 = l_lean_ir_terminator_check___closed__1;
lean::inc(x_41);
x_3 = x_41;
x_4 = x_23;
goto lbl_5;
}
else
{
obj* x_43; 
x_43 = l_lean_ir_match__type___closed__5;
lean::inc(x_43);
x_3 = x_43;
x_4 = x_23;
goto lbl_5;
}
}
else
{
obj* x_46; 
lean::dec(x_35);
x_46 = l_lean_ir_match__type___closed__5;
lean::inc(x_46);
x_3 = x_46;
x_4 = x_23;
goto lbl_5;
}
}
}
default:
{
obj* x_49; 
lean::dec(x_1);
x_49 = l_lean_ir_match__type___closed__5;
lean::inc(x_49);
x_3 = x_49;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_51; obj* x_53; obj* x_54; uint8 x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_3, 0);
lean::inc(x_51);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_53 = x_3;
}
x_54 = l_lean_ir_terminator_to__format___main(x_0);
x_55 = 0;
x_56 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_55);
x_59 = x_58;
x_60 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_55);
x_63 = x_62;
x_64 = lean::box(1);
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_55);
x_66 = x_65;
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_51);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_55);
x_68 = x_67;
if (lean::is_scalar(x_53)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_53;
}
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_4);
return x_70;
}
else
{
obj* x_72; 
lean::dec(x_0);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_3);
lean::cnstr_set(x_72, 1, x_4);
return x_72;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_phi_check(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_instr_check(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_block_check(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
lean::inc(x_1);
x_11 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__1(x_3, x_1, x_2);
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
x_25 = l_list_mmap_x_27___main___at_lean_ir_block_check___spec__2(x_22, x_1, x_14);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_39; uint8 x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
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
x_39 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_36);
x_40 = 0;
x_41 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_40);
x_44 = x_43;
x_45 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_40);
x_48 = x_47;
x_49 = lean::box(1);
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
x_57 = l_lean_ir_terminator_check(x_5, x_1, x_8);
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
obj* x_63; obj* x_66; obj* x_69; uint8 x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_63 = lean::cnstr_get(x_58, 0);
lean::inc(x_63);
lean::dec(x_58);
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
x_69 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_66);
x_70 = 0;
x_71 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_71);
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_70);
x_74 = x_73;
x_75 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_75);
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_75);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_70);
x_78 = x_77;
x_79 = lean::box(1);
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
 lean::cnstr_set_tag(x_56, 0);
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
lean::dec(x_0);
lean::dec(x_56);
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
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_block_check(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_11 = l_list_mmap_x_27___main___at_lean_ir_decl_check___main___spec__1(x_8, x_1, x_2);
return x_11;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; 
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
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_type__check___spec__2___rarg), 4, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
x_11 = l_lean_ir_decl_header___main(x_0);
x_12 = lean::cnstr_get(x_11, 2);
lean::inc(x_12);
lean::dec(x_11);
x_15 = l_lean_ir_type__checker__m_run___rarg(x_10, x_1, x_12);
return x_15;
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
 l_lean_ir_is__nonfloat__arith__ty___closed__1 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__1();
 l_lean_ir_is__nonfloat__arith__ty___closed__2 = _init_l_lean_ir_is__nonfloat__arith__ty___closed__2();
 l_lean_ir_valid__assign__unop__types___closed__1 = _init_l_lean_ir_valid__assign__unop__types___closed__1();
 l_lean_ir_valid__assign__unop__types___closed__2 = _init_l_lean_ir_valid__assign__unop__types___closed__2();
 l_lean_ir_valid__assign__unop__types___closed__3 = _init_l_lean_ir_valid__assign__unop__types___closed__3();
 l_lean_ir_valid__assign__unop__types___closed__4 = _init_l_lean_ir_valid__assign__unop__types___closed__4();
 l_lean_ir_type__checker__m = _init_l_lean_ir_type__checker__m();
 l_lean_ir_match__type___closed__1 = _init_l_lean_ir_match__type___closed__1();
 l_lean_ir_match__type___closed__2 = _init_l_lean_ir_match__type___closed__2();
 l_lean_ir_match__type___closed__3 = _init_l_lean_ir_match__type___closed__3();
 l_lean_ir_match__type___closed__4 = _init_l_lean_ir_match__type___closed__4();
 l_lean_ir_match__type___closed__5 = _init_l_lean_ir_match__type___closed__5();
 l_lean_ir_get__type___closed__1 = _init_l_lean_ir_get__type___closed__1();
 l_lean_ir_check__type___closed__1 = _init_l_lean_ir_check__type___closed__1();
 l_lean_ir_check__type___closed__2 = _init_l_lean_ir_check__type___closed__2();
 l_lean_ir_check__ne__type___closed__1 = _init_l_lean_ir_check__ne__type___closed__1();
 l_lean_ir_check__ne__type___closed__2 = _init_l_lean_ir_check__ne__type___closed__2();
 l_lean_ir_invalid__literal___rarg___closed__1 = _init_l_lean_ir_invalid__literal___rarg___closed__1();
 l_lean_ir_get__decl___closed__1 = _init_l_lean_ir_get__decl___closed__1();
 l_lean_ir_check__arg__types___main___closed__1 = _init_l_lean_ir_check__arg__types___main___closed__1();
 l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_instr_check___spec__2___closed__1();
 l_lean_ir_instr_check___closed__1 = _init_l_lean_ir_instr_check___closed__1();
 l_lean_ir_instr_check___closed__2 = _init_l_lean_ir_instr_check___closed__2();
 l_lean_ir_instr_check___closed__3 = _init_l_lean_ir_instr_check___closed__3();
 l_lean_ir_instr_check___closed__4 = _init_l_lean_ir_instr_check___closed__4();
 l_lean_ir_instr_check___closed__5 = _init_l_lean_ir_instr_check___closed__5();
 l_lean_ir_terminator_check___closed__1 = _init_l_lean_ir_terminator_check___closed__1();
 l_lean_ir_type__check___closed__1 = _init_l_lean_ir_type__check___closed__1();
}
