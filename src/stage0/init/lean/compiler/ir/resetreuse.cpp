// Lean compiler output
// Module: init.lean.compiler.ir.resetreuse
// Imports: init.control.state init.control.reader init.lean.compiler.ir.basic init.lean.compiler.ir.livevars init.lean.compiler.ir.format
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
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_setBody(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_IR_ResetReuse_R___main(obj*, obj*, obj*);
obj* l_Lean_IR_MaxIndex_collectDecl(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___boxed(obj*);
obj* l_Lean_IR_FnBody_body(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addJP(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___boxed(obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_resetreuse_9__D(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_getPrefix(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar(obj*, obj*);
uint8 l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_hasLiveVar(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_insertResetReuse(obj*);
uint8 l_Lean_IR_FnBody_isTerminal(obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main___boxed(obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ResetReuse_R(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_9__D___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_1__mayReuse___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_resetreuse_2__S(obj*, obj*, obj*);
uint8 l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 2);
x_4 = lean::cnstr_get(x_2, 2);
x_5 = lean::nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_1, 3);
x_8 = lean::cnstr_get(x_2, 3);
x_9 = lean::nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8 x_10; 
x_10 = 0;
return x_10;
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_1, 4);
x_12 = lean::cnstr_get(x_2, 4);
x_13 = lean::nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = 0;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = l_Lean_Name_getPrefix(x_15);
x_17 = lean::cnstr_get(x_2, 0);
x_18 = l_Lean_Name_getPrefix(x_17);
x_19 = lean_name_dec_eq(x_16, x_18);
lean::dec(x_18);
lean::dec(x_16);
return x_19;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_1__mayReuse___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_4;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::array_fget(x_4, x_3);
x_10 = lean::box(0);
lean::inc(x_9);
x_11 = x_10;
x_12 = lean::array_fset(x_4, x_3, x_11);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
if (lean::obj_tag(x_9) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::inc(x_1);
x_17 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = x_18;
x_20 = lean::array_fset(x_12, x_3, x_19);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_20;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_9, 0);
lean::inc(x_22);
lean::inc(x_1);
x_23 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = x_24;
x_26 = lean::array_fset(x_12, x_3, x_25);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_26;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_12; 
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_14 = lean::cnstr_get(x_3, 2);
x_15 = lean::cnstr_get(x_3, 1);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
x_18 = l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(x_2, x_16);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_17);
lean::dec(x_16);
x_19 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_14);
lean::cnstr_set(x_3, 2, x_19);
return x_3;
}
else
{
obj* x_20; obj* x_21; uint8 x_22; 
lean::dec(x_12);
x_20 = lean::cnstr_get(x_2, 1);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
uint8 x_23; obj* x_24; 
x_23 = 1;
x_24 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_24, 0, x_1);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_17);
lean::cnstr_set_scalar(x_24, sizeof(void*)*3, x_23);
lean::cnstr_set(x_3, 1, x_24);
return x_3;
}
else
{
uint8 x_25; obj* x_26; 
x_25 = 0;
x_26 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_16);
lean::cnstr_set(x_26, 2, x_17);
lean::cnstr_set_scalar(x_26, sizeof(void*)*3, x_25);
lean::cnstr_set(x_3, 1, x_26);
return x_3;
}
}
}
else
{
obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_27 = lean::cnstr_get(x_3, 0);
x_28 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*3);
x_29 = lean::cnstr_get(x_3, 2);
lean::inc(x_29);
lean::inc(x_27);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_12, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_12, 1);
lean::inc(x_31);
x_32 = l___private_init_lean_compiler_ir_resetreuse_1__mayReuse(x_2, x_30);
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_31);
lean::dec(x_30);
x_33 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_29);
x_34 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_34, 0, x_27);
lean::cnstr_set(x_34, 1, x_12);
lean::cnstr_set(x_34, 2, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*3, x_28);
return x_34;
}
else
{
obj* x_35; obj* x_36; uint8 x_37; 
lean::dec(x_12);
x_35 = lean::cnstr_get(x_2, 1);
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
x_37 = lean::nat_dec_eq(x_35, x_36);
lean::dec(x_36);
if (x_37 == 0)
{
uint8 x_38; obj* x_39; obj* x_40; 
x_38 = 1;
x_39 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_39, 0, x_1);
lean::cnstr_set(x_39, 1, x_30);
lean::cnstr_set(x_39, 2, x_31);
lean::cnstr_set_scalar(x_39, sizeof(void*)*3, x_38);
x_40 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_40, 0, x_27);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set(x_40, 2, x_29);
lean::cnstr_set_scalar(x_40, sizeof(void*)*3, x_28);
return x_40;
}
else
{
uint8 x_41; obj* x_42; obj* x_43; 
x_41 = 0;
x_42 = lean::alloc_cnstr(2, 3, 1);
lean::cnstr_set(x_42, 0, x_1);
lean::cnstr_set(x_42, 1, x_30);
lean::cnstr_set(x_42, 2, x_31);
lean::cnstr_set_scalar(x_42, sizeof(void*)*3, x_41);
x_43 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_43, 0, x_27);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set(x_43, 2, x_29);
lean::cnstr_set_scalar(x_43, sizeof(void*)*3, x_28);
return x_43;
}
}
}
}
else
{
obj* x_44; 
lean::dec(x_12);
x_44 = lean::box(0);
x_4 = x_44;
goto block_11;
}
}
case 1:
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_3);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; uint8 x_49; 
x_46 = lean::cnstr_get(x_3, 2);
x_47 = lean::cnstr_get(x_3, 3);
lean::inc(x_46);
lean::inc(x_1);
x_48 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_46);
lean::inc(x_48);
lean::inc(x_46);
x_49 = l_Lean_IR_FnBody_beq(x_46, x_48);
if (x_49 == 0)
{
lean::dec(x_46);
lean::dec(x_1);
lean::cnstr_set(x_3, 2, x_48);
return x_3;
}
else
{
obj* x_50; 
lean::dec(x_48);
x_50 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_47);
lean::cnstr_set(x_3, 3, x_50);
return x_3;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; 
x_51 = lean::cnstr_get(x_3, 0);
x_52 = lean::cnstr_get(x_3, 1);
x_53 = lean::cnstr_get(x_3, 2);
x_54 = lean::cnstr_get(x_3, 3);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_3);
lean::inc(x_53);
lean::inc(x_1);
x_55 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_53);
lean::inc(x_55);
lean::inc(x_53);
x_56 = l_Lean_IR_FnBody_beq(x_53, x_55);
if (x_56 == 0)
{
obj* x_57; 
lean::dec(x_53);
lean::dec(x_1);
x_57 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_57, 0, x_51);
lean::cnstr_set(x_57, 1, x_52);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_54);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_55);
x_58 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_54);
x_59 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_59, 0, x_51);
lean::cnstr_set(x_59, 1, x_52);
lean::cnstr_set(x_59, 2, x_53);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
case 10:
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_3);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = lean::cnstr_get(x_3, 2);
x_62 = lean::mk_nat_obj(0u);
x_63 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(x_1, x_2, x_62, x_61);
lean::cnstr_set(x_3, 2, x_63);
return x_3;
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_3, 0);
x_65 = lean::cnstr_get(x_3, 1);
x_66 = lean::cnstr_get(x_3, 2);
lean::inc(x_66);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_3);
x_67 = lean::mk_nat_obj(0u);
x_68 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(x_1, x_2, x_67, x_66);
x_69 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_65);
lean::cnstr_set(x_69, 2, x_68);
return x_69;
}
}
default: 
{
obj* x_70; 
x_70 = lean::box(0);
x_4 = x_70;
goto block_11;
}
}
block_11:
{
uint8 x_5; 
lean::dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = l_Lean_IR_FnBody_body(x_3);
x_7 = lean::box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_3, x_7);
x_9 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_6);
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_9);
return x_10;
}
else
{
lean::dec(x_1);
return x_3;
}
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_2__S___main___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_2__S___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_resetreuse_2__S(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg), 1, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_resetreuse_3__mkFresh(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_3__mkFresh___rarg(x_5);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_3);
lean::inc(x_8);
x_9 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_8, x_2, x_3);
lean::inc(x_9);
lean::inc(x_3);
x_10 = l_Lean_IR_FnBody_beq(x_3, x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; obj* x_14; 
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_1);
x_13 = 7;
x_14 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_9);
lean::cnstr_set_scalar(x_14, sizeof(void*)*3, x_13);
lean::cnstr_set(x_6, 0, x_14);
return x_6;
}
else
{
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_1);
lean::cnstr_set(x_6, 0, x_3);
return x_6;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_15 = lean::cnstr_get(x_6, 0);
x_16 = lean::cnstr_get(x_6, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_6);
lean::inc(x_3);
lean::inc(x_15);
x_17 = l___private_init_lean_compiler_ir_resetreuse_2__S___main(x_15, x_2, x_3);
lean::inc(x_17);
lean::inc(x_3);
x_18 = l_Lean_IR_FnBody_beq(x_3, x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
lean::dec(x_3);
x_19 = lean::cnstr_get(x_2, 2);
lean::inc(x_19);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_1);
x_21 = 7;
x_22 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_22, 0, x_15);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set(x_22, 2, x_17);
lean::cnstr_set_scalar(x_22, sizeof(void*)*3, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_16);
return x_23;
}
else
{
obj* x_24; 
lean::dec(x_17);
lean::dec(x_15);
lean::dec(x_1);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_16);
return x_24;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_4__tryS___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_7 = lean::unbox(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_1, x_2, x_8, x_4, x_5);
return x_9;
}
else
{
uint8 x_10; 
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_3);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_3, 1);
lean::dec(x_11);
lean::cnstr_set(x_3, 1, x_5);
return x_3;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_5);
return x_13;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
uint8 l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::array_fget(x_2, x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
return x_9;
}
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
goto _start;
}
}
}
}
uint8 l___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1(x_2, x_1, x_3);
return x_4;
}
}
obj* l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_3, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_anyMAux___main___at___private_init_lean_compiler_ir_resetreuse_6__argsContainsVar___spec__1(x_2, x_4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::array_fget(x_4, x_3);
x_13 = lean::box(0);
lean::inc(x_12);
x_14 = x_13;
x_15 = lean::array_fset(x_4, x_3, x_14);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::inc(x_5);
lean::inc(x_1);
x_18 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_17, x_5, x_6);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
lean::inc(x_1);
x_21 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(x_1, x_2, x_19, x_5, x_20);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
lean::dec(x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_add(x_3, x_25);
x_27 = x_24;
x_28 = lean::array_fset(x_15, x_3, x_27);
lean::dec(x_3);
x_3 = x_26;
x_4 = x_28;
x_6 = x_23;
goto _start;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_30 = lean::cnstr_get(x_12, 0);
lean::inc(x_30);
lean::inc(x_5);
lean::inc(x_1);
x_31 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_30, x_5, x_6);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
lean::dec(x_31);
lean::inc(x_1);
x_34 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(x_1, x_2, x_32, x_5, x_33);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_34, 1);
lean::inc(x_36);
lean::dec(x_34);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_35);
x_38 = lean::mk_nat_obj(1u);
x_39 = lean::nat_add(x_3, x_38);
x_40 = x_37;
x_41 = lean::array_fset(x_15, x_3, x_40);
lean::dec(x_3);
x_3 = x_39;
x_4 = x_41;
x_6 = x_36;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
switch (lean::obj_tag(x_3)) {
case 1:
{
uint8 x_91; 
x_91 = !lean::is_exclusive(x_3);
if (x_91 == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; 
x_92 = lean::cnstr_get(x_3, 0);
x_93 = lean::cnstr_get(x_3, 1);
x_94 = lean::cnstr_get(x_3, 2);
x_95 = lean::cnstr_get(x_3, 3);
lean::inc(x_94);
lean::inc(x_93);
lean::inc(x_92);
lean::inc(x_4);
x_96 = l_Lean_IR_LocalContext_addJP(x_4, x_92, x_93, x_94);
lean::inc(x_1);
x_97 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_95, x_96, x_5);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_97, 1);
lean::inc(x_99);
lean::dec(x_97);
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
x_102 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_94, x_4, x_99);
x_103 = !lean::is_exclusive(x_102);
if (x_103 == 0)
{
obj* x_104; uint8 x_105; 
x_104 = lean::cnstr_get(x_102, 0);
x_105 = !lean::is_exclusive(x_104);
if (x_105 == 0)
{
obj* x_106; obj* x_107; 
x_106 = lean::cnstr_get(x_104, 0);
x_107 = lean::cnstr_get(x_104, 1);
lean::dec(x_107);
lean::cnstr_set(x_3, 3, x_100);
lean::cnstr_set(x_3, 2, x_106);
lean::cnstr_set(x_104, 1, x_101);
lean::cnstr_set(x_104, 0, x_3);
return x_102;
}
else
{
obj* x_108; obj* x_109; 
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
lean::dec(x_104);
lean::cnstr_set(x_3, 3, x_100);
lean::cnstr_set(x_3, 2, x_108);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_3);
lean::cnstr_set(x_109, 1, x_101);
lean::cnstr_set(x_102, 0, x_109);
return x_102;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_110 = lean::cnstr_get(x_102, 0);
x_111 = lean::cnstr_get(x_102, 1);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_110, 0);
lean::inc(x_112);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_113 = x_110;
} else {
 lean::dec_ref(x_110);
 x_113 = lean::box(0);
}
lean::cnstr_set(x_3, 3, x_100);
lean::cnstr_set(x_3, 2, x_112);
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_3);
lean::cnstr_set(x_114, 1, x_101);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_111);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_116 = lean::cnstr_get(x_3, 0);
x_117 = lean::cnstr_get(x_3, 1);
x_118 = lean::cnstr_get(x_3, 2);
x_119 = lean::cnstr_get(x_3, 3);
lean::inc(x_119);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_3);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::inc(x_4);
x_120 = l_Lean_IR_LocalContext_addJP(x_4, x_116, x_117, x_118);
lean::inc(x_1);
x_121 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_119, x_120, x_5);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_121, 1);
lean::inc(x_123);
lean::dec(x_121);
x_124 = lean::cnstr_get(x_122, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
x_126 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_118, x_4, x_123);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_126, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 lean::cnstr_release(x_126, 1);
 x_129 = x_126;
} else {
 lean::dec_ref(x_126);
 x_129 = lean::box(0);
}
x_130 = lean::cnstr_get(x_127, 0);
lean::inc(x_130);
if (lean::is_exclusive(x_127)) {
 lean::cnstr_release(x_127, 0);
 lean::cnstr_release(x_127, 1);
 x_131 = x_127;
} else {
 lean::dec_ref(x_127);
 x_131 = lean::box(0);
}
x_132 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_132, 0, x_116);
lean::cnstr_set(x_132, 1, x_117);
lean::cnstr_set(x_132, 2, x_130);
lean::cnstr_set(x_132, 3, x_124);
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_125);
if (lean::is_scalar(x_129)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_129;
}
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_128);
return x_134;
}
}
case 10:
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; uint8 x_139; 
x_135 = lean::cnstr_get(x_3, 0);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_3, 1);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_3, 2);
lean::inc(x_137);
lean::inc(x_4);
x_138 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
x_139 = lean::unbox(x_138);
lean::dec(x_138);
if (x_139 == 0)
{
uint8 x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_137);
lean::dec(x_136);
lean::dec(x_135);
lean::dec(x_4);
lean::dec(x_1);
x_140 = 0;
x_141 = lean::box(x_140);
x_142 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_142, 0, x_3);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_5);
return x_143;
}
else
{
uint8 x_144; 
x_144 = !lean::is_exclusive(x_3);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; uint8 x_150; 
x_145 = lean::cnstr_get(x_3, 2);
lean::dec(x_145);
x_146 = lean::cnstr_get(x_3, 1);
lean::dec(x_146);
x_147 = lean::cnstr_get(x_3, 0);
lean::dec(x_147);
x_148 = lean::mk_nat_obj(0u);
x_149 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1(x_1, x_2, x_148, x_137, x_4, x_5);
x_150 = !lean::is_exclusive(x_149);
if (x_150 == 0)
{
obj* x_151; obj* x_152; uint8 x_153; obj* x_154; obj* x_155; 
x_151 = lean::cnstr_get(x_149, 0);
x_152 = lean::cnstr_get(x_149, 1);
lean::cnstr_set(x_3, 2, x_151);
x_153 = 1;
x_154 = lean::box(x_153);
lean::cnstr_set(x_149, 1, x_154);
lean::cnstr_set(x_149, 0, x_3);
x_155 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_155, 0, x_149);
lean::cnstr_set(x_155, 1, x_152);
return x_155;
}
else
{
obj* x_156; obj* x_157; uint8 x_158; obj* x_159; obj* x_160; obj* x_161; 
x_156 = lean::cnstr_get(x_149, 0);
x_157 = lean::cnstr_get(x_149, 1);
lean::inc(x_157);
lean::inc(x_156);
lean::dec(x_149);
lean::cnstr_set(x_3, 2, x_156);
x_158 = 1;
x_159 = lean::box(x_158);
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_3);
lean::cnstr_set(x_160, 1, x_159);
x_161 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_157);
return x_161;
}
}
else
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; uint8 x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_3);
x_162 = lean::mk_nat_obj(0u);
x_163 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1(x_1, x_2, x_162, x_137, x_4, x_5);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 x_166 = x_163;
} else {
 lean::dec_ref(x_163);
 x_166 = lean::box(0);
}
x_167 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_167, 0, x_135);
lean::cnstr_set(x_167, 1, x_136);
lean::cnstr_set(x_167, 2, x_164);
x_168 = 1;
x_169 = lean::box(x_168);
if (lean::is_scalar(x_166)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_166;
}
lean::cnstr_set(x_170, 0, x_167);
lean::cnstr_set(x_170, 1, x_169);
x_171 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_165);
return x_171;
}
}
}
default: 
{
obj* x_172; 
x_172 = lean::box(0);
x_6 = x_172;
goto block_90;
}
}
block_90:
{
uint8 x_7; 
lean::dec(x_6);
x_7 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = l_Lean_IR_FnBody_body(x_3);
x_9 = lean::box(13);
lean::inc(x_3);
x_10 = l_Lean_IR_FnBody_setBody(x_3, x_9);
x_11 = l___private_init_lean_compiler_ir_resetreuse_7__isCtorUsing(x_10, x_1);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
lean::dec(x_3);
lean::inc(x_4);
lean::inc(x_1);
x_12 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_8, x_4, x_5);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_12);
if (x_16 == 0)
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_12, 1);
x_18 = lean::cnstr_get(x_12, 0);
lean::dec(x_18);
x_19 = !lean::is_exclusive(x_13);
if (x_19 == 0)
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = lean::cnstr_get(x_13, 0);
x_21 = lean::cnstr_get(x_13, 1);
lean::dec(x_21);
x_22 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_22 == 0)
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_1);
x_23 = l_Lean_IR_FnBody_setBody(x_10, x_20);
lean::cnstr_set(x_13, 0, x_23);
return x_12;
}
else
{
obj* x_24; uint8 x_25; 
lean::free_heap_obj(x_12);
lean::dec(x_14);
x_24 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_1, x_2, x_20, x_4, x_17);
lean::dec(x_4);
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
x_28 = l_Lean_IR_FnBody_setBody(x_10, x_26);
x_29 = 1;
x_30 = lean::box(x_29);
lean::cnstr_set(x_24, 1, x_30);
lean::cnstr_set(x_24, 0, x_28);
lean::cnstr_set(x_13, 1, x_27);
lean::cnstr_set(x_13, 0, x_24);
return x_13;
}
else
{
obj* x_31; obj* x_32; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_24, 0);
x_32 = lean::cnstr_get(x_24, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_24);
x_33 = l_Lean_IR_FnBody_setBody(x_10, x_31);
x_34 = 1;
x_35 = lean::box(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set(x_13, 1, x_32);
lean::cnstr_set(x_13, 0, x_36);
return x_13;
}
}
}
else
{
obj* x_37; uint8 x_38; 
x_37 = lean::cnstr_get(x_13, 0);
lean::inc(x_37);
lean::dec(x_13);
x_38 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_38 == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_4);
lean::dec(x_1);
x_39 = l_Lean_IR_FnBody_setBody(x_10, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_14);
lean::cnstr_set(x_12, 0, x_40);
return x_12;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::free_heap_obj(x_12);
lean::dec(x_14);
x_41 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_1, x_2, x_37, x_4, x_17);
lean::dec(x_4);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_44 = x_41;
} else {
 lean::dec_ref(x_41);
 x_44 = lean::box(0);
}
x_45 = l_Lean_IR_FnBody_setBody(x_10, x_42);
x_46 = 1;
x_47 = lean::box(x_46);
if (lean::is_scalar(x_44)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_44;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_43);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_12, 1);
lean::inc(x_50);
lean::dec(x_12);
x_51 = lean::cnstr_get(x_13, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_52 = x_13;
} else {
 lean::dec_ref(x_13);
 x_52 = lean::box(0);
}
x_53 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_4);
lean::dec(x_1);
x_54 = l_Lean_IR_FnBody_setBody(x_10, x_51);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_14);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_50);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_14);
x_57 = l___private_init_lean_compiler_ir_resetreuse_4__tryS(x_1, x_2, x_51, x_4, x_50);
lean::dec(x_4);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_60 = x_57;
} else {
 lean::dec_ref(x_57);
 x_60 = lean::box(0);
}
x_61 = l_Lean_IR_FnBody_setBody(x_10, x_58);
x_62 = 1;
x_63 = lean::box(x_62);
if (lean::is_scalar(x_60)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_60;
}
lean::cnstr_set(x_64, 0, x_61);
lean::cnstr_set(x_64, 1, x_63);
if (lean::is_scalar(x_52)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_52;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_59);
return x_65;
}
}
}
else
{
uint8 x_66; 
lean::dec(x_4);
lean::dec(x_1);
x_66 = !lean::is_exclusive(x_12);
if (x_66 == 0)
{
obj* x_67; uint8 x_68; 
x_67 = lean::cnstr_get(x_12, 0);
lean::dec(x_67);
x_68 = !lean::is_exclusive(x_13);
if (x_68 == 0)
{
obj* x_69; obj* x_70; obj* x_71; 
x_69 = lean::cnstr_get(x_13, 0);
x_70 = lean::cnstr_get(x_13, 1);
lean::dec(x_70);
x_71 = l_Lean_IR_FnBody_setBody(x_10, x_69);
lean::cnstr_set(x_13, 0, x_71);
return x_12;
}
else
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_13, 0);
lean::inc(x_72);
lean::dec(x_13);
x_73 = l_Lean_IR_FnBody_setBody(x_10, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_14);
lean::cnstr_set(x_12, 0, x_74);
return x_12;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_75 = lean::cnstr_get(x_12, 1);
lean::inc(x_75);
lean::dec(x_12);
x_76 = lean::cnstr_get(x_13, 0);
lean::inc(x_76);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_77 = x_13;
} else {
 lean::dec_ref(x_13);
 x_77 = lean::box(0);
}
x_78 = l_Lean_IR_FnBody_setBody(x_10, x_76);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_14);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_75);
return x_80;
}
}
}
else
{
uint8 x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_1);
x_81 = 1;
x_82 = lean::box(x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_3);
lean::cnstr_set(x_83, 1, x_82);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_5);
return x_84;
}
}
else
{
obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
x_85 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
lean::dec(x_1);
x_86 = lean::unbox(x_85);
lean::dec(x_85);
x_87 = lean::box(x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_3);
lean::cnstr_set(x_88, 1, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_5);
return x_89;
}
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_8__Dmain___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_9__D(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_4);
lean::inc(x_1);
x_6 = l___private_init_lean_compiler_ir_resetreuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = l___private_init_lean_compiler_ir_resetreuse_5__Dfinalize(x_1, x_2, x_7, x_4, x_8);
lean::dec(x_4);
return x_9;
}
}
obj* l___private_init_lean_compiler_ir_resetreuse_9__D___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_resetreuse_9__D(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::array_fget(x_3, x_2);
x_12 = lean::box(0);
lean::inc(x_11);
x_13 = x_12;
x_14 = lean::array_fset(x_3, x_2, x_13);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::inc(x_4);
x_17 = l_Lean_IR_ResetReuse_R___main(x_16, x_4, x_5);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
lean::inc(x_18);
lean::inc(x_15);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_IR_CtorInfo_isScalar(x_15);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_20);
lean::inc(x_4);
lean::inc(x_1);
x_22 = l___private_init_lean_compiler_ir_resetreuse_9__D(x_1, x_15, x_18, x_4, x_19);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_15);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::mk_nat_obj(1u);
x_27 = lean::nat_add(x_2, x_26);
x_28 = x_25;
x_29 = lean::array_fset(x_14, x_2, x_28);
lean::dec(x_2);
x_2 = x_27;
x_3 = x_29;
x_5 = x_24;
goto _start;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_18);
lean::dec(x_15);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_2, x_31);
x_33 = x_20;
x_34 = lean::array_fset(x_14, x_2, x_33);
lean::dec(x_2);
x_2 = x_32;
x_3 = x_34;
x_5 = x_19;
goto _start;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_11, 0);
lean::inc(x_36);
lean::inc(x_4);
x_37 = l_Lean_IR_ResetReuse_R___main(x_36, x_4, x_5);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_37, 1);
lean::inc(x_39);
lean::dec(x_37);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_38);
x_41 = lean::mk_nat_obj(1u);
x_42 = lean::nat_add(x_2, x_41);
x_43 = x_40;
x_44 = lean::array_fset(x_14, x_2, x_43);
lean::dec(x_2);
x_2 = x_42;
x_3 = x_44;
x_5 = x_39;
goto _start;
}
}
}
}
obj* l_Lean_IR_ResetReuse_R___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
switch (lean::obj_tag(x_1)) {
case 1:
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_1);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_2);
x_24 = l_Lean_IR_ResetReuse_R___main(x_22, x_2, x_3);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_24, 1);
lean::inc(x_26);
lean::dec(x_24);
lean::inc(x_25);
lean::inc(x_21);
lean::inc(x_20);
x_27 = l_Lean_IR_LocalContext_addJP(x_2, x_20, x_21, x_25);
x_28 = l_Lean_IR_ResetReuse_R___main(x_23, x_27, x_26);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; 
x_30 = lean::cnstr_get(x_28, 0);
lean::cnstr_set(x_1, 3, x_30);
lean::cnstr_set(x_1, 2, x_25);
lean::cnstr_set(x_28, 0, x_1);
return x_28;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_28, 0);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_28);
lean::cnstr_set(x_1, 3, x_31);
lean::cnstr_set(x_1, 2, x_25);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_34 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_1, 2);
x_37 = lean::cnstr_get(x_1, 3);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_1);
lean::inc(x_2);
x_38 = l_Lean_IR_ResetReuse_R___main(x_36, x_2, x_3);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
lean::inc(x_39);
lean::inc(x_35);
lean::inc(x_34);
x_41 = l_Lean_IR_LocalContext_addJP(x_2, x_34, x_35, x_39);
x_42 = l_Lean_IR_ResetReuse_R___main(x_37, x_41, x_40);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_46 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_46, 0, x_34);
lean::cnstr_set(x_46, 1, x_35);
lean::cnstr_set(x_46, 2, x_39);
lean::cnstr_set(x_46, 3, x_43);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
}
case 10:
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_1);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; uint8 x_53; 
x_49 = lean::cnstr_get(x_1, 1);
x_50 = lean::cnstr_get(x_1, 2);
x_51 = lean::mk_nat_obj(0u);
lean::inc(x_49);
x_52 = l_Array_ummapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(x_49, x_51, x_50, x_2, x_3);
x_53 = !lean::is_exclusive(x_52);
if (x_53 == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_52, 0);
lean::cnstr_set(x_1, 2, x_54);
lean::cnstr_set(x_52, 0, x_1);
return x_52;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_52, 0);
x_56 = lean::cnstr_get(x_52, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_52);
lean::cnstr_set(x_1, 2, x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_1);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_58 = lean::cnstr_get(x_1, 0);
x_59 = lean::cnstr_get(x_1, 1);
x_60 = lean::cnstr_get(x_1, 2);
lean::inc(x_60);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_1);
x_61 = lean::mk_nat_obj(0u);
lean::inc(x_59);
x_62 = l_Array_ummapAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(x_59, x_61, x_60, x_2, x_3);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_62, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_65 = x_62;
} else {
 lean::dec_ref(x_62);
 x_65 = lean::box(0);
}
x_66 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_66, 0, x_58);
lean::cnstr_set(x_66, 1, x_59);
lean::cnstr_set(x_66, 2, x_63);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_64);
return x_67;
}
}
default: 
{
obj* x_68; 
x_68 = lean::box(0);
x_4 = x_68;
goto block_18;
}
}
block_18:
{
uint8 x_5; 
lean::dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = l_Lean_IR_FnBody_body(x_1);
x_7 = lean::box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_1, x_7);
x_9 = l_Lean_IR_ResetReuse_R___main(x_6, x_2, x_3);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_Lean_IR_FnBody_setBody(x_8, x_11);
lean::cnstr_set(x_9, 0, x_12);
return x_9;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_9);
x_15 = l_Lean_IR_FnBody_setBody(x_8, x_13);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
}
else
{
obj* x_17; 
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
}
}
}
obj* l_Lean_IR_ResetReuse_R(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_ResetReuse_R___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Decl_insertResetReuse(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_7 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_6);
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_1, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_7, x_12);
lean::dec(x_7);
x_14 = lean::box(0);
x_15 = l_Lean_IR_ResetReuse_R___main(x_5, x_14, x_13);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
lean::cnstr_set(x_1, 2, x_16);
return x_1;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_1);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_7, x_17);
lean::dec(x_7);
x_19 = lean::box(0);
x_20 = l_Lean_IR_ResetReuse_R___main(x_5, x_19, x_18);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
x_22 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_22, 0, x_2);
lean::cnstr_set(x_22, 1, x_3);
lean::cnstr_set(x_22, 2, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*3, x_4);
return x_22;
}
}
else
{
return x_1;
}
}
}
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_livevars(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
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
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
return w;
}
