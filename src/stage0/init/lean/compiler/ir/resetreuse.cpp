// Lean compiler output
// Module: init.lean.compiler.ir.resetreuse
// Imports: init.control.state init.control.reader init.lean.compiler.ir.basic init.lean.compiler.ir.livevars
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
obj* l_Array_hmmapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_ResetReuse_R___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___boxed(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__D(obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl___main(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addJP(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main(obj*, obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___boxed(obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_FnBody_hasLiveVar(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_insertResetReuse(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg___boxed(obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj*, obj*);
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix___main(obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___rarg(obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Lean_IR_ResetReuse_R(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_1__mayReuse___boxed(obj*, obj*);
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
obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_56; uint8 x_59; 
x_44 = lean::cnstr_get(x_2, 0);
x_46 = lean::cnstr_get(x_2, 1);
x_48 = lean::cnstr_get(x_2, 2);
x_50 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_52 = x_2;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_2);
 x_52 = lean::box(0);
}
lean::inc(x_48);
lean::inc(x_1);
lean::inc(x_0);
x_56 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_48);
lean::inc(x_56);
lean::inc(x_48);
x_59 = l_Lean_IR_FnBody_beq(x_48, x_56);
if (x_59 == 0)
{
obj* x_63; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_48);
if (lean::is_scalar(x_52)) {
 x_63 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_63 = x_52;
}
lean::cnstr_set(x_63, 0, x_44);
lean::cnstr_set(x_63, 1, x_46);
lean::cnstr_set(x_63, 2, x_56);
lean::cnstr_set(x_63, 3, x_50);
return x_63;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_56);
x_65 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_50);
if (lean::is_scalar(x_52)) {
 x_66 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_66 = x_52;
}
lean::cnstr_set(x_66, 0, x_44);
lean::cnstr_set(x_66, 1, x_46);
lean::cnstr_set(x_66, 2, x_48);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
case 9:
{
obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_67 = lean::cnstr_get(x_2, 0);
x_69 = lean::cnstr_get(x_2, 1);
x_71 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 x_73 = x_2;
} else {
 lean::inc(x_67);
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_2);
 x_73 = lean::box(0);
}
x_74 = lean::mk_nat_obj(0ul);
x_75 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(x_0, x_1, x_74, x_71);
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_67);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_75);
return x_76;
}
default:
{
obj* x_77; 
x_77 = lean::box(0);
x_3 = x_77;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_79; 
lean::dec(x_3);
x_79 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_79 == 0)
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_80 = l_Lean_IR_FnBody_body___main(x_2);
x_81 = lean::box(12);
x_82 = l_Lean_IR_FnBody_setBody___main(x_2, x_81);
x_83 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_0, x_1, x_80);
x_84 = l_Lean_IR_FnBody_setBody___main(x_82, x_83);
return x_84;
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
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(obj* x_0) {
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
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_17; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(x_4);
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_6);
x_14 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_6, x_1, x_2);
lean::inc(x_14);
lean::inc(x_2);
x_17 = l_Lean_IR_FnBody_beq(x_2, x_14);
if (x_17 == 0)
{
obj* x_19; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_2);
x_19 = lean::cnstr_get(x_1, 2);
lean::inc(x_19);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_0);
x_23 = 7;
x_24 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_22);
lean::cnstr_set(x_24, 2, x_14);
lean::cnstr_set_scalar(x_24, sizeof(void*)*3, x_23);
x_25 = x_24;
if (lean::is_scalar(x_10)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_10;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_8);
return x_26;
}
else
{
obj* x_31; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
if (lean::is_scalar(x_10)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_10;
}
lean::cnstr_set(x_31, 0, x_2);
lean::cnstr_set(x_31, 1, x_8);
return x_31;
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_7; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::unbox(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_0, x_1, x_8, x_3, x_4);
return x_11;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 x_16 = x_2;
} else {
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_4);
return x_17;
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_13; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_5);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::array_fget(x_3, x_2);
x_15 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
x_16 = lean::array_fset(x_3, x_2, x_15);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_25; obj* x_26; obj* x_28; obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_17 = lean::cnstr_get(x_14, 0);
x_19 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 x_21 = x_14;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_14);
 x_21 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_19, x_4, x_5);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
lean::inc(x_1);
lean::inc(x_0);
x_33 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_26, x_4, x_28);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::is_scalar(x_21)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_21;
}
lean::cnstr_set(x_39, 0, x_17);
lean::cnstr_set(x_39, 1, x_34);
x_40 = lean::mk_nat_obj(1ul);
x_41 = lean::nat_add(x_2, x_40);
x_42 = lean::array_fset(x_16, x_2, x_39);
lean::dec(x_2);
x_2 = x_41;
x_3 = x_42;
x_5 = x_36;
goto _start;
}
else
{
obj* x_45; obj* x_47; obj* x_51; obj* x_52; obj* x_54; obj* x_59; obj* x_60; obj* x_62; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_45 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_47 = x_14;
} else {
 lean::inc(x_45);
 lean::dec(x_14);
 x_47 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_51 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_45, x_4, x_5);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
lean::inc(x_1);
lean::inc(x_0);
x_59 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_52, x_4, x_54);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_60);
x_66 = lean::mk_nat_obj(1ul);
x_67 = lean::nat_add(x_2, x_66);
x_68 = lean::array_fset(x_16, x_2, x_65);
lean::dec(x_2);
x_2 = x_67;
x_3 = x_68;
x_5 = x_62;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_7 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
x_11 = lean::cnstr_get(x_2, 2);
x_13 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 x_15 = x_2;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_9);
lean::inc(x_7);
lean::inc(x_3);
x_20 = l_Lean_IR_LocalContext_addJP(x_3, x_7, x_9, x_11);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_13, x_20, x_4);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_11, x_3, x_26);
x_33 = lean::cnstr_get(x_32, 0);
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_32);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_43 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_43 = x_15;
}
lean::cnstr_set(x_43, 0, x_7);
lean::cnstr_set(x_43, 1, x_9);
lean::cnstr_set(x_43, 2, x_38);
lean::cnstr_set(x_43, 3, x_29);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_40);
if (lean::is_scalar(x_37)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_37;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_35);
return x_45;
}
case 9:
{
obj* x_46; obj* x_48; obj* x_50; obj* x_54; uint8 x_55; 
x_46 = lean::cnstr_get(x_2, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_2, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_2, 2);
lean::inc(x_50);
lean::inc(x_3);
lean::inc(x_2);
x_54 = l_Lean_IR_FnBody_hasLiveVar(x_2, x_3, x_0);
x_55 = lean::unbox(x_54);
if (x_55 == 0)
{
uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_48);
lean::dec(x_50);
lean::dec(x_46);
x_62 = 0;
x_63 = lean::box(x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_2);
lean::cnstr_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_4);
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_66 = x_2;
} else {
 lean::dec(x_2);
 x_66 = lean::box(0);
}
x_67 = lean::mk_nat_obj(0ul);
x_68 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_6__Dmain___main___spec__1(x_0, x_1, x_67, x_50, x_3, x_4);
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_73 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_68);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_74 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_74 = x_66;
}
lean::cnstr_set(x_74, 0, x_46);
lean::cnstr_set(x_74, 1, x_48);
lean::cnstr_set(x_74, 2, x_69);
x_75 = 1;
x_76 = lean::box(x_75);
if (lean::is_scalar(x_73)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_73;
}
lean::cnstr_set(x_77, 0, x_74);
lean::cnstr_set(x_77, 1, x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_71);
return x_78;
}
}
default:
{
obj* x_79; 
x_79 = lean::box(0);
x_5 = x_79;
goto lbl_6;
}
}
lbl_6:
{
uint8 x_81; 
lean::dec(x_5);
x_81 = l_Lean_IR_FnBody_isTerminal___main(x_2);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_88; obj* x_89; obj* x_91; uint8 x_93; 
x_82 = l_Lean_IR_FnBody_body___main(x_2);
x_83 = lean::box(12);
x_84 = l_Lean_IR_FnBody_setBody___main(x_2, x_83);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_88 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_82, x_3, x_4);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
x_93 = lean::unbox(x_91);
if (x_93 == 0)
{
obj* x_94; obj* x_96; obj* x_97; obj* x_99; uint8 x_100; 
x_94 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_set(x_88, 1, lean::box(0));
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
x_97 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_set(x_89, 0, lean::box(0));
 lean::cnstr_release(x_89, 1);
 x_99 = x_89;
} else {
 lean::inc(x_97);
 lean::dec(x_89);
 x_99 = lean::box(0);
}
x_100 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_84);
if (x_100 == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_104 = l_Lean_IR_FnBody_setBody___main(x_84, x_97);
if (lean::is_scalar(x_99)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_99;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_91);
if (lean::is_scalar(x_96)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_96;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_94);
return x_106;
}
else
{
obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_96);
x_108 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_0, x_1, x_97, x_3, x_94);
lean::dec(x_3);
x_110 = lean::cnstr_get(x_108, 0);
x_112 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 x_114 = x_108;
} else {
 lean::inc(x_110);
 lean::inc(x_112);
 lean::dec(x_108);
 x_114 = lean::box(0);
}
x_115 = l_Lean_IR_FnBody_setBody___main(x_84, x_110);
x_116 = 1;
x_117 = lean::box(x_116);
if (lean::is_scalar(x_114)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_114;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_117);
if (lean::is_scalar(x_99)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_99;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_112);
return x_119;
}
}
else
{
obj* x_123; obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_123 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_125 = x_88;
} else {
 lean::inc(x_123);
 lean::dec(x_88);
 x_125 = lean::box(0);
}
x_126 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 1);
 x_128 = x_89;
} else {
 lean::inc(x_126);
 lean::dec(x_89);
 x_128 = lean::box(0);
}
x_129 = l_Lean_IR_FnBody_setBody___main(x_84, x_126);
if (lean::is_scalar(x_128)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_128;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_91);
if (lean::is_scalar(x_125)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_125;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_123);
return x_131;
}
}
else
{
obj* x_134; obj* x_136; obj* x_137; 
lean::dec(x_1);
lean::inc(x_2);
x_134 = l_Lean_IR_FnBody_hasLiveVar(x_2, x_3, x_0);
lean::dec(x_0);
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_2);
lean::cnstr_set(x_136, 1, x_134);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_4);
return x_137;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_6__Dmain(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
uint8 l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_8; 
x_8 = lean::array_fget(x_1, x_2);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; uint8 x_12; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (x_12 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_2, x_14);
lean::dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean::dec(x_2);
return x_12;
}
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1ul);
x_20 = lean::nat_add(x_2, x_19);
lean::dec(x_2);
x_2 = x_20;
goto _start;
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
x_14 = l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(x_5, x_10, x_13);
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
case 1:
{
obj* x_22; obj* x_24; uint8 x_27; 
x_22 = lean::cnstr_get(x_0, 2);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_0, 3);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(x_22);
if (x_27 == 0)
{
x_0 = x_24;
goto _start;
}
else
{
uint8 x_30; 
lean::dec(x_24);
x_30 = 1;
return x_30;
}
}
default:
{
obj* x_31; 
x_31 = lean::box(0);
x_1 = x_31;
goto lbl_2;
}
}
lbl_2:
{
uint8 x_33; 
lean::dec(x_1);
x_33 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_33 == 0)
{
obj* x_34; 
x_34 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_34;
goto _start;
}
else
{
uint8 x_38; 
lean::dec(x_0);
x_38 = 0;
return x_38;
}
}
}
}
obj* l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main___spec__1(x_0, x_1, x_2);
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
obj* l___private_init_lean_compiler_ir_resetreuse_8__D(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_6; 
lean::inc(x_2);
x_6 = l___private_init_lean_compiler_ir_resetreuse_7__hasCtorUsing___main(x_2);
if (x_6 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_16; 
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l___private_init_lean_compiler_ir_resetreuse_6__Dmain___main(x_0, x_1, x_2, x_3, x_4);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___main(x_0, x_1, x_11, x_3, x_13);
lean::dec(x_3);
return x_16;
}
else
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_4);
return x_21;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_fget(x_2, x_1);
x_13 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1;
x_14 = lean::array_fset(x_2, x_1, x_13);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_29; uint8 x_30; 
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
lean::inc(x_3);
x_21 = l_Lean_IR_ResetReuse_R___main(x_17, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
lean::inc(x_22);
lean::inc(x_15);
if (lean::is_scalar(x_19)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_19;
}
lean::cnstr_set(x_29, 0, x_15);
lean::cnstr_set(x_29, 1, x_22);
x_30 = l_Lean_IR_CtorInfo_isScalar(x_15);
if (x_30 == 0)
{
obj* x_35; obj* x_36; obj* x_38; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_29);
lean::inc(x_3);
lean::inc(x_15);
lean::inc(x_0);
x_35 = l___private_init_lean_compiler_ir_resetreuse_8__D(x_0, x_15, x_22, x_3, x_24);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_15);
lean::cnstr_set(x_41, 1, x_36);
x_42 = lean::mk_nat_obj(1ul);
x_43 = lean::nat_add(x_1, x_42);
x_44 = lean::array_fset(x_14, x_1, x_41);
lean::dec(x_1);
x_1 = x_43;
x_2 = x_44;
x_4 = x_38;
goto _start;
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_22);
lean::dec(x_15);
x_49 = lean::mk_nat_obj(1ul);
x_50 = lean::nat_add(x_1, x_49);
x_51 = lean::array_fset(x_14, x_1, x_29);
lean::dec(x_1);
x_1 = x_50;
x_2 = x_51;
x_4 = x_24;
goto _start;
}
}
else
{
obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_54 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_56 = x_12;
} else {
 lean::inc(x_54);
 lean::dec(x_12);
 x_56 = lean::box(0);
}
lean::inc(x_3);
x_58 = l_Lean_IR_ResetReuse_R___main(x_54, x_3, x_4);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::is_scalar(x_56)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_56;
}
lean::cnstr_set(x_64, 0, x_59);
x_65 = lean::mk_nat_obj(1ul);
x_66 = lean::nat_add(x_1, x_65);
x_67 = lean::array_fset(x_14, x_1, x_64);
lean::dec(x_1);
x_1 = x_66;
x_2 = x_67;
x_4 = x_61;
goto _start;
}
}
}
}
obj* l_Lean_IR_ResetReuse_R___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_5 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_9 = lean::cnstr_get(x_0, 2);
x_11 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_13 = x_0;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_0);
 x_13 = lean::box(0);
}
lean::inc(x_1);
x_15 = l_Lean_IR_ResetReuse_R___main(x_9, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
lean::inc(x_16);
lean::inc(x_7);
lean::inc(x_5);
x_24 = l_Lean_IR_LocalContext_addJP(x_1, x_5, x_7, x_16);
x_25 = l_Lean_IR_ResetReuse_R___main(x_11, x_24, x_18);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_13;
}
lean::cnstr_set(x_31, 0, x_5);
lean::cnstr_set(x_31, 1, x_7);
lean::cnstr_set(x_31, 2, x_16);
lean::cnstr_set(x_31, 3, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
case 9:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_33 = lean::cnstr_get(x_0, 0);
x_35 = lean::cnstr_get(x_0, 1);
x_37 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_39 = x_0;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_0);
 x_39 = lean::box(0);
}
x_40 = lean::mk_nat_obj(0ul);
lean::inc(x_35);
x_42 = l_Array_hmmapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(x_35, x_40, x_37, x_1, x_2);
x_43 = lean::cnstr_get(x_42, 0);
x_45 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_47 = x_42;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_42);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_48 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_48 = x_39;
}
lean::cnstr_set(x_48, 0, x_33);
lean::cnstr_set(x_48, 1, x_35);
lean::cnstr_set(x_48, 2, x_43);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
return x_49;
}
default:
{
obj* x_50; 
x_50 = lean::box(0);
x_3 = x_50;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_52; 
lean::dec(x_3);
x_52 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_53 = l_Lean_IR_FnBody_body___main(x_0);
x_54 = lean::box(12);
x_55 = l_Lean_IR_FnBody_setBody___main(x_0, x_54);
x_56 = l_Lean_IR_ResetReuse_R___main(x_53, x_1, x_2);
x_57 = lean::cnstr_get(x_56, 0);
x_59 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_61 = x_56;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = l_Lean_IR_FnBody_setBody___main(x_55, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
return x_63;
}
else
{
obj* x_65; 
lean::dec(x_1);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_0);
lean::cnstr_set(x_65, 1, x_2);
return x_65;
}
}
}
}
obj* l_Lean_IR_ResetReuse_R(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_ResetReuse_R___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Decl_insertResetReuse___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_10 = l_Lean_IR_MaxIndex_collectDecl___main(x_0, x_8);
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
x_15 = lean::box(0);
x_16 = l_Lean_IR_ResetReuse_R___main(x_6, x_15, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_3);
lean::cnstr_set(x_20, 2, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*3, x_5);
x_21 = x_20;
return x_21;
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
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_livevars(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_resetreuse(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_livevars(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___closed__1);
return w;
}
