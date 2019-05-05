// Lean compiler output
// Module: init.lean.compiler.ir.resetreuse
// Imports: init.default init.lean.compiler.ir.basic init.control.state
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
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_9__R(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__D(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main(obj*, obj*, obj*);
obj* l_Lean_IR_MaxVar_collectDecl___main(obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(obj*, obj*, obj*, obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_9__R___main(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___boxed(obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_Decl_insertResetReuse(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg___boxed(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj*, obj*);
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
uint8 l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj*, obj*, obj*, obj*);
obj* l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix___main(obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg(obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_1__mayReuse___boxed(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArg___main(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___boxed(obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 2);
x_3 = lean::cnstr_get(x_1, 2);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 3);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = lean::nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_0, 4);
x_11 = lean::cnstr_get(x_1, 4);
x_12 = lean::nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_14 = lean::cnstr_get(x_0, 0);
x_15 = l_Lean_Name_getPrefix___main(x_14);
x_16 = lean::cnstr_get(x_1, 0);
x_17 = l_Lean_Name_getPrefix___main(x_16);
x_18 = lean_name_dec_eq(x_15, x_17);
lean::dec(x_17);
lean::dec(x_15);
return x_18;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_1__mayReuse___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(12);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_fget(x_3, x_2);
x_11 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
x_12 = lean::array_fset(x_3, x_2, x_11);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_0);
x_22 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_17);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::array_fset(x_12, x_2, x_23);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_24;
goto _start;
}
else
{
obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_29 = x_10;
} else {
 lean::inc(x_27);
 lean::dec(x_10);
 x_29 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_0);
x_32 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_27);
if (lean::is_scalar(x_29)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_29;
}
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::array_fset(x_12, x_2, x_33);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_34;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_5; obj* x_6; 
x_5 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; uint8 x_17; 
x_8 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_release(x_2, 1);
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_12 = x_2;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_2);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_6, 1);
lean::inc(x_15);
x_17 = l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(x_1, x_13);
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_13);
lean::dec(x_15);
x_20 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_10);
if (lean::is_scalar(x_12)) {
 x_21 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_21 = x_12;
}
lean::cnstr_set(x_21, 0, x_8);
lean::cnstr_set(x_21, 1, x_6);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*3, x_5);
x_22 = x_21;
return x_22;
}
else
{
obj* x_24; obj* x_26; uint8 x_29; 
lean::dec(x_6);
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_13, 1);
lean::inc(x_26);
lean::dec(x_13);
x_29 = lean::nat_dec_eq(x_24, x_26);
lean::dec(x_26);
lean::dec(x_24);
if (x_29 == 0)
{
uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = 1;
x_33 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_33, 0, x_0);
lean::cnstr_set(x_33, 1, x_1);
lean::cnstr_set(x_33, 2, x_15);
lean::cnstr_set_scalar(x_33, sizeof(void*)*3, x_32);
x_34 = x_33;
if (lean::is_scalar(x_12)) {
 x_35 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_35 = x_12;
}
lean::cnstr_set(x_35, 0, x_8);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set(x_35, 2, x_10);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_5);
x_36 = x_35;
return x_36;
}
else
{
uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = 0;
x_38 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_38, 0, x_0);
lean::cnstr_set(x_38, 1, x_1);
lean::cnstr_set(x_38, 2, x_15);
lean::cnstr_set_scalar(x_38, sizeof(void*)*3, x_37);
x_39 = x_38;
if (lean::is_scalar(x_12)) {
 x_40 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_40 = x_12;
}
lean::cnstr_set(x_40, 0, x_8);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set(x_40, 2, x_10);
lean::cnstr_set_scalar(x_40, sizeof(void*)*3, x_5);
x_41 = x_40;
return x_41;
}
}
}
default:
{
obj* x_43; 
lean::dec(x_6);
x_43 = lean::box(0);
x_3 = x_43;
goto lbl_4;
}
}
}
case 1:
{
obj* x_44; obj* x_46; uint8 x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_57; uint8 x_60; 
x_44 = lean::cnstr_get(x_2, 0);
x_46 = lean::cnstr_get(x_2, 1);
x_48 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
x_49 = lean::cnstr_get(x_2, 2);
x_51 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_53 = x_2;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_2);
 x_53 = lean::box(0);
}
lean::inc(x_49);
lean::inc(x_1);
lean::inc(x_0);
x_57 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_49);
lean::inc(x_57);
lean::inc(x_49);
x_60 = l_Lean_IR_FnBody_beq(x_49, x_57);
if (x_60 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_49);
if (lean::is_scalar(x_53)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_53;
}
lean::cnstr_set(x_64, 0, x_44);
lean::cnstr_set(x_64, 1, x_46);
lean::cnstr_set(x_64, 2, x_57);
lean::cnstr_set(x_64, 3, x_51);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_48);
x_65 = x_64;
return x_65;
}
else
{
obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_57);
x_67 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_51);
if (lean::is_scalar(x_53)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_53;
}
lean::cnstr_set(x_68, 0, x_44);
lean::cnstr_set(x_68, 1, x_46);
lean::cnstr_set(x_68, 2, x_49);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_48);
x_69 = x_68;
return x_69;
}
}
case 9:
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_2, 0);
x_72 = lean::cnstr_get(x_2, 1);
x_74 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_76 = x_2;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_2);
 x_76 = lean::box(0);
}
x_77 = lean::mk_nat_obj(0ul);
x_78 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(x_0, x_1, x_77, x_74);
if (lean::is_scalar(x_76)) {
 x_79 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_79 = x_76;
}
lean::cnstr_set(x_79, 0, x_70);
lean::cnstr_set(x_79, 1, x_72);
lean::cnstr_set(x_79, 2, x_78);
return x_79;
}
default:
{
obj* x_80; 
x_80 = lean::box(0);
x_3 = x_80;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_82; 
lean::dec(x_3);
x_82 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_83 = l_Lean_IR_FnBody_body___main(x_2);
x_84 = lean::box(12);
x_85 = l_Lean_IR_FnBody_setBody___main(x_2, x_84);
x_86 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_83);
x_87 = l_Lean_IR_FnBody_setBody___main(x_85, x_86);
return x_87;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::nat_add(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_15; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(x_3);
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
lean::inc(x_2);
lean::inc(x_5);
x_12 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_5, x_1, x_2);
lean::inc(x_12);
lean::inc(x_2);
x_15 = l_Lean_IR_FnBody_beq(x_2, x_12);
if (x_15 == 0)
{
obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_2);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_0);
x_18 = 7;
x_19 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 2, x_12);
lean::cnstr_set_scalar(x_19, sizeof(void*)*3, x_18);
x_20 = x_19;
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_25; 
lean::dec(x_5);
lean::dec(x_12);
lean::dec(x_0);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_9;
}
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_7);
return x_25;
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_6 = lean::unbox(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_0, x_1, x_7, x_3);
return x_10;
}
else
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_3);
return x_16;
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_3);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_fget(x_3, x_2);
x_13 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
x_14 = lean::array_fset(x_3, x_2, x_13);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_15 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_0);
x_22 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_17, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
lean::inc(x_1);
lean::inc(x_0);
x_30 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_23, x_25);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::is_scalar(x_19)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_19;
}
lean::cnstr_set(x_36, 0, x_15);
lean::cnstr_set(x_36, 1, x_31);
x_37 = lean::mk_nat_obj(1ul);
x_38 = lean::nat_add(x_2, x_37);
x_39 = lean::array_fset(x_14, x_2, x_36);
lean::dec(x_2);
x_2 = x_38;
x_3 = x_39;
x_4 = x_33;
goto _start;
}
else
{
obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_50; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_42 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_44 = x_12;
} else {
 lean::inc(x_42);
 lean::dec(x_12);
 x_44 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_0);
x_47 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_42, x_4);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
lean::inc(x_1);
lean::inc(x_0);
x_55 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_48, x_50);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::is_scalar(x_44)) {
 x_61 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_61 = x_44;
}
lean::cnstr_set(x_61, 0, x_56);
x_62 = lean::mk_nat_obj(1ul);
x_63 = lean::nat_add(x_2, x_62);
x_64 = lean::array_fset(x_14, x_2, x_61);
lean::dec(x_2);
x_2 = x_63;
x_3 = x_64;
x_4 = x_58;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_6; obj* x_8; obj* x_10; uint8 x_12; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 2);
lean::inc(x_10);
x_12 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_2);
if (x_12 == 0)
{
uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_18 = 0;
x_19 = lean::box(x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_2);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_22 = x_2;
} else {
 lean::dec(x_2);
 x_22 = lean::box(0);
}
x_23 = lean::mk_nat_obj(0ul);
x_24 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(x_0, x_1, x_23, x_10, x_3);
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_29 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_30 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_30 = x_22;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_25);
x_31 = 1;
x_32 = lean::box(x_31);
if (lean::is_scalar(x_29)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_29;
}
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
}
default:
{
obj* x_35; 
x_35 = lean::box(0);
x_4 = x_35;
goto lbl_5;
}
}
lbl_5:
{
uint8 x_37; 
lean::dec(x_4);
x_37 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; uint8 x_48; 
x_38 = l_Lean_IR_FnBody_body___main(x_2);
x_39 = lean::box(12);
x_40 = l_Lean_IR_FnBody_setBody___main(x_2, x_39);
lean::inc(x_1);
lean::inc(x_0);
x_43 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_38, x_3);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
x_48 = lean::unbox(x_46);
if (x_48 == 0)
{
obj* x_49; obj* x_51; obj* x_52; obj* x_54; uint8 x_55; 
x_49 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_set(x_43, 1, lean::box(0));
 x_51 = x_43;
} else {
 lean::inc(x_49);
 lean::dec(x_43);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_set(x_44, 0, lean::box(0));
 lean::cnstr_release(x_44, 1);
 x_54 = x_44;
} else {
 lean::inc(x_52);
 lean::dec(x_44);
 x_54 = lean::box(0);
}
x_55 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_40);
if (x_55 == 0)
{
obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_1);
lean::dec(x_0);
x_58 = l_Lean_IR_FnBody_setBody___main(x_40, x_52);
if (lean::is_scalar(x_54)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_54;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_46);
if (lean::is_scalar(x_51)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_51;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_49);
return x_60;
}
else
{
obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_51);
x_62 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_0, x_1, x_52, x_49);
x_63 = lean::cnstr_get(x_62, 0);
x_65 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 x_67 = x_62;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_62);
 x_67 = lean::box(0);
}
x_68 = l_Lean_IR_FnBody_setBody___main(x_40, x_63);
x_69 = 1;
x_70 = lean::box(x_69);
if (lean::is_scalar(x_67)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_67;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
if (lean::is_scalar(x_54)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_54;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
}
else
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_1);
lean::dec(x_0);
x_75 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_77 = x_43;
} else {
 lean::inc(x_75);
 lean::dec(x_43);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 1);
 x_80 = x_44;
} else {
 lean::inc(x_78);
 lean::dec(x_44);
 x_80 = lean::box(0);
}
x_81 = l_Lean_IR_FnBody_setBody___main(x_40, x_78);
if (lean::is_scalar(x_80)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_80;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_46);
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_75);
return x_83;
}
}
else
{
uint8 x_85; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_85 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_2);
lean::dec(x_0);
x_87 = lean::box(x_85);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_2);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_3);
return x_89;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
uint8 l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8 x_16; 
lean::dec(x_2);
x_16 = 1;
return x_16;
}
}
}
}
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(obj* x_0) {
_start:
{
obj* x_1; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::mk_nat_obj(0ul);
x_14 = l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(x_5, x_10, x_13);
lean::dec(x_10);
lean::dec(x_5);
if (x_14 == 0)
{
x_0 = x_7;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_7);
x_19 = 1;
return x_19;
}
}
default:
{
obj* x_21; 
lean::dec(x_3);
x_21 = lean::box(0);
x_1 = x_21;
goto lbl_2;
}
}
}
default:
{
obj* x_22; 
x_22 = lean::box(0);
x_1 = x_22;
goto lbl_2;
}
}
lbl_2:
{
uint8 x_24; 
lean::dec(x_1);
x_24 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_24 == 0)
{
obj* x_25; 
x_25 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_25;
goto _start;
}
else
{
uint8 x_29; 
lean::dec(x_0);
x_29 = 0;
return x_29;
}
}
}
}
obj* l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_8__D(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; 
lean::inc(x_2);
x_5 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(x_2);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
lean::inc(x_1);
lean::inc(x_0);
x_8 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_9, x_11);
return x_14;
}
else
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(12);
x_10 = lean::array_fset(x_1, x_0, x_9);
switch (lean::obj_tag(x_8)) {
case 1:
{
obj* x_14; obj* x_16; uint8 x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_30; obj* x_31; 
x_14 = lean::cnstr_get(x_8, 0);
x_16 = lean::cnstr_get(x_8, 1);
x_18 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*4);
x_19 = lean::cnstr_get(x_8, 2);
x_21 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_23 = x_8;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_8);
 x_23 = lean::box(0);
}
x_24 = l___private_init_lean_compiler_ir_resetreuse_9__R___main(x_19, x_2);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::is_scalar(x_23)) {
 x_30 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_30 = x_23;
}
lean::cnstr_set(x_30, 0, x_14);
lean::cnstr_set(x_30, 1, x_16);
lean::cnstr_set(x_30, 2, x_25);
lean::cnstr_set(x_30, 3, x_21);
lean::cnstr_set_scalar(x_30, sizeof(void*)*4, x_18);
x_31 = x_30;
x_11 = x_31;
x_12 = x_27;
goto lbl_13;
}
default:
{
x_11 = x_8;
x_12 = x_2;
goto lbl_13;
}
}
lbl_13:
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::mk_nat_obj(1ul);
x_33 = lean::nat_add(x_0, x_32);
x_34 = lean::array_fset(x_10, x_0, x_11);
lean::dec(x_0);
x_0 = x_33;
x_1 = x_34;
x_2 = x_12;
goto _start;
}
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_2, x_1);
x_11 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
x_12 = lean::array_fset(x_2, x_1, x_11);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_13 = lean::cnstr_get(x_10, 0);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = l___private_init_lean_compiler_ir_resetreuse_9__R___main(x_15, x_3);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
lean::inc(x_13);
lean::inc(x_0);
x_26 = l___private_init_lean_compiler_ir_resetreuse_8__D(x_0, x_13, x_19, x_21);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_13);
lean::cnstr_set(x_32, 1, x_27);
x_33 = lean::mk_nat_obj(1ul);
x_34 = lean::nat_add(x_1, x_33);
x_35 = lean::array_fset(x_12, x_1, x_32);
lean::dec(x_1);
x_1 = x_34;
x_2 = x_35;
x_3 = x_29;
goto _start;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_40 = x_10;
} else {
 lean::inc(x_38);
 lean::dec(x_10);
 x_40 = lean::box(0);
}
x_41 = l___private_init_lean_compiler_ir_resetreuse_9__R___main(x_38, x_3);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::is_scalar(x_40)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_40;
}
lean::cnstr_set(x_47, 0, x_42);
x_48 = lean::mk_nat_obj(1ul);
x_49 = lean::nat_add(x_1, x_48);
x_50 = lean::array_fset(x_12, x_1, x_47);
lean::dec(x_1);
x_1 = x_49;
x_2 = x_50;
x_3 = x_44;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_9__R___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_2 = l_Lean_IR_FnBody_flatten(x_0);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__1(x_8, x_3, x_1);
switch (lean::obj_tag(x_5)) {
case 9:
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_5, 0);
x_17 = lean::cnstr_get(x_5, 1);
x_19 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 x_21 = x_5;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_5);
 x_21 = lean::box(0);
}
lean::inc(x_17);
x_23 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_9__R___main___spec__2(x_17, x_8, x_19, x_12);
x_24 = lean::cnstr_get(x_23, 0);
x_26 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 x_28 = x_23;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_29 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_29 = x_21;
}
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_17);
lean::cnstr_set(x_29, 2, x_24);
x_30 = l_Lean_IR_reshape(x_10, x_29);
if (lean::is_scalar(x_28)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_28;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_26);
return x_31;
}
default:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_9, 0);
x_34 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_36 = x_9;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_9);
 x_36 = lean::box(0);
}
x_37 = l_Lean_IR_reshape(x_32, x_5);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
return x_38;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_9__R(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_resetreuse_9__R___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_insertResetReuse___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_20; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_10 = l_Lean_IR_MaxVar_collectDecl___main(x_0, x_8);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_11 = x_0;
} else {
 lean::dec(x_0);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_10, x_12);
lean::dec(x_10);
x_15 = l___private_init_lean_compiler_ir_resetreuse_9__R___main(x_6, x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
if (lean::is_scalar(x_11)) {
 x_19 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_19 = x_11;
}
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_3);
lean::cnstr_set(x_19, 2, x_16);
lean::cnstr_set_scalar(x_19, sizeof(void*)*3, x_5);
x_20 = x_19;
return x_20;
}
else
{
return x_0;
}
}
}
obj* l_Lean_IR_Decl_insertResetReuse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_insertResetReuse___main(x_0);
return x_1;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_control_state(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_resetreuse(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1);
return w;
}
