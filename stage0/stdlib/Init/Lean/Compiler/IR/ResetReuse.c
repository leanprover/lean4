// Lean compiler output
// Module: Init.Lean.Compiler.IR.ResetReuse
// Imports: Init.Control.State Init.Control.Reader Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.LiveVars Init.Lean.Compiler.IR.Format
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_9__D___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_IR_HasIndex_visitFnBody___main(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_9__D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse(lean_object*, lean_object*);
lean_object* l_Lean_IR_ResetReuse_R___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___rarg(lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_hasLiveVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ResetReuse_R(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Lean_Name_getPrefix(x_15);
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_Lean_Name_getPrefix(x_17);
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
return x_19;
}
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_4;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_3);
x_10 = lean_box(0);
x_11 = x_10;
x_12 = lean_array_fset(x_4, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_1);
x_17 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = x_18;
lean_dec(x_9);
x_20 = lean_array_fset(x_12, x_3, x_19);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_inc(x_1);
x_23 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = x_24;
lean_dec(x_9);
x_26 = lean_array_fset(x_12, x_3, x_25);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_26;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse(x_2, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_14);
lean_ctor_set(x_3, 3, x_19);
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_12);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = 1;
x_24 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
lean_ctor_set(x_3, 2, x_24);
return x_3;
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
lean_ctor_set(x_3, 2, x_26);
return x_3;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
x_32 = l___private_Init_Lean_Compiler_IR_ResetReuse_1__mayReuse(x_2, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_30);
x_33 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_29);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_12);
lean_ctor_set(x_34, 3, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_12);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_29);
return x_40;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_28);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_29);
return x_43;
}
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
x_44 = lean_box(0);
x_4 = x_44;
goto block_11;
}
}
case 1:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_3, 2);
x_47 = lean_ctor_get(x_3, 3);
lean_inc(x_46);
lean_inc(x_1);
x_48 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_46);
lean_inc(x_48);
lean_inc(x_46);
x_49 = l_Lean_IR_FnBody_beq(x_46, x_48);
if (x_49 == 0)
{
lean_dec(x_46);
lean_dec(x_1);
lean_ctor_set(x_3, 2, x_48);
return x_3;
}
else
{
lean_object* x_50; 
lean_dec(x_48);
x_50 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_47);
lean_ctor_set(x_3, 3, x_50);
return x_3;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
x_53 = lean_ctor_get(x_3, 2);
x_54 = lean_ctor_get(x_3, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
lean_inc(x_53);
lean_inc(x_1);
x_55 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_53);
lean_inc(x_55);
lean_inc(x_53);
x_56 = l_Lean_IR_FnBody_beq(x_53, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_1);
x_57 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
x_58 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_54);
x_59 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_52);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_58);
return x_59;
}
}
}
case 10:
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_3, 3);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1(x_1, x_2, x_62, x_61);
lean_ctor_set(x_3, 3, x_63);
return x_3;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
x_66 = lean_ctor_get(x_3, 2);
x_67 = lean_ctor_get(x_3, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_3);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1(x_1, x_2, x_68, x_67);
x_70 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set(x_70, 3, x_69);
return x_70;
}
}
default: 
{
lean_object* x_71; 
x_71 = lean_box(0);
x_4 = x_71;
goto block_11;
}
}
block_11:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_IR_FnBody_body(x_3);
x_7 = lean_box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_3, x_7);
x_9 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_6);
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_9);
return x_10;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_3__mkFresh___rarg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_3);
lean_inc(x_8);
x_9 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_8, x_2, x_3);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Lean_IR_FnBody_beq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_15);
x_17 = l___private_Init_Lean_Compiler_IR_ResetReuse_2__S___main(x_15, x_2, x_3);
lean_inc(x_17);
lean_inc(x_3);
x_18 = l_Lean_IR_FnBody_beq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
x_21 = lean_box(7);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(x_1, x_2, x_8, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_5);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_nat_dec_eq(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l___private_Init_Lean_Compiler_IR_ResetReuse_6__argsContainsVar(x_4, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_4, x_3);
x_13 = lean_box(0);
x_14 = x_13;
x_15 = lean_array_fset(x_4, x_3, x_14);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_17, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_1);
x_21 = l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(x_1, x_2, x_19, x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_3, x_25);
x_27 = x_24;
lean_dec(x_12);
x_28 = lean_array_fset(x_15, x_3, x_27);
lean_dec(x_3);
x_3 = x_26;
x_4 = x_28;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_inc(x_5);
lean_inc(x_1);
x_31 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_30, x_5, x_6);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_1);
x_34 = l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(x_1, x_2, x_32, x_5, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_3, x_38);
x_40 = x_37;
lean_dec(x_12);
x_41 = lean_array_fset(x_15, x_3, x_40);
lean_dec(x_3);
x_3 = x_39;
x_4 = x_41;
x_6 = x_36;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_3);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_92 = lean_ctor_get(x_3, 0);
x_93 = lean_ctor_get(x_3, 1);
x_94 = lean_ctor_get(x_3, 2);
x_95 = lean_ctor_get(x_3, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_4);
x_96 = l_Lean_IR_LocalContext_addJP(x_4, x_92, x_93, x_94);
lean_inc(x_1);
x_97 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_95, x_96, x_5);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_94, x_4, x_99);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_dec(x_107);
lean_ctor_set(x_3, 3, x_100);
lean_ctor_set(x_3, 2, x_106);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 0, x_3);
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
lean_dec(x_104);
lean_ctor_set(x_3, 3, x_100);
lean_ctor_set(x_3, 2, x_108);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_3);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_102, 0, x_109);
return x_102;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_102, 0);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_102);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
lean_ctor_set(x_3, 3, x_100);
lean_ctor_set(x_3, 2, x_112);
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_3);
lean_ctor_set(x_114, 1, x_101);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_116 = lean_ctor_get(x_3, 0);
x_117 = lean_ctor_get(x_3, 1);
x_118 = lean_ctor_get(x_3, 2);
x_119 = lean_ctor_get(x_3, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_4);
x_120 = l_Lean_IR_LocalContext_addJP(x_4, x_116, x_117, x_118);
lean_inc(x_1);
x_121 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_119, x_120, x_5);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_118, x_4, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_132, 0, x_116);
lean_ctor_set(x_132, 1, x_117);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_124);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_125);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_128);
return x_134;
}
}
case 10:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_3, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_3, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 3);
lean_inc(x_138);
lean_inc(x_4);
lean_inc(x_3);
x_139 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_4);
lean_dec(x_1);
x_141 = 0;
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_3);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_5);
return x_144;
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_3);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_146 = lean_ctor_get(x_3, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_3, 2);
lean_dec(x_147);
x_148 = lean_ctor_get(x_3, 1);
lean_dec(x_148);
x_149 = lean_ctor_get(x_3, 0);
lean_dec(x_149);
x_150 = lean_unsigned_to_nat(0u);
x_151 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1(x_1, x_2, x_150, x_138, x_4, x_5);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
lean_ctor_set(x_3, 3, x_153);
x_155 = 1;
x_156 = lean_box(x_155);
lean_ctor_set(x_151, 1, x_156);
lean_ctor_set(x_151, 0, x_3);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_151, 0);
x_159 = lean_ctor_get(x_151, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_151);
lean_ctor_set(x_3, 3, x_158);
x_160 = 1;
x_161 = lean_box(x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_3);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_3);
x_164 = lean_unsigned_to_nat(0u);
x_165 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1(x_1, x_2, x_164, x_138, x_4, x_5);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_169, 0, x_135);
lean_ctor_set(x_169, 1, x_136);
lean_ctor_set(x_169, 2, x_137);
lean_ctor_set(x_169, 3, x_166);
x_170 = 1;
x_171 = lean_box(x_170);
if (lean_is_scalar(x_168)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_168;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_167);
return x_173;
}
}
}
default: 
{
lean_object* x_174; 
x_174 = lean_box(0);
x_6 = x_174;
goto block_90;
}
}
block_90:
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_IR_FnBody_body(x_3);
x_9 = lean_box(13);
lean_inc(x_3);
x_10 = l_Lean_IR_FnBody_setBody(x_3, x_9);
x_11 = l___private_Init_Lean_Compiler_IR_ResetReuse_7__isCtorUsing(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_8, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_dec(x_21);
x_22 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_1);
x_23 = l_Lean_IR_FnBody_setBody(x_10, x_20);
lean_ctor_set(x_13, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_free_object(x_12);
lean_dec(x_14);
x_24 = l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(x_1, x_2, x_20, x_4, x_17);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_IR_FnBody_setBody(x_10, x_26);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_24, 1, x_30);
lean_ctor_set(x_24, 0, x_28);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = l_Lean_IR_FnBody_setBody(x_10, x_31);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_13, 0, x_36);
return x_13;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
lean_dec(x_1);
x_39 = l_Lean_IR_FnBody_setBody(x_10, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_12);
lean_dec(x_14);
x_41 = l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(x_1, x_2, x_37, x_4, x_17);
lean_dec(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_IR_FnBody_setBody(x_10, x_42);
x_46 = 1;
x_47 = lean_box(x_46);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_ctor_get(x_13, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_52 = x_13;
} else {
 lean_dec_ref(x_13);
 x_52 = lean_box(0);
}
x_53 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_10);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
lean_dec(x_1);
x_54 = l_Lean_IR_FnBody_setBody(x_10, x_51);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_14);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_14);
x_57 = l___private_Init_Lean_Compiler_IR_ResetReuse_4__tryS(x_1, x_2, x_51, x_4, x_50);
lean_dec(x_4);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l_Lean_IR_FnBody_setBody(x_10, x_58);
x_62 = 1;
x_63 = lean_box(x_62);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_52)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_52;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_4);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_12);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_12, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_13);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_13, 0);
x_70 = lean_ctor_get(x_13, 1);
lean_dec(x_70);
x_71 = l_Lean_IR_FnBody_setBody(x_10, x_69);
lean_ctor_set(x_13, 0, x_71);
return x_12;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
lean_dec(x_13);
x_73 = l_Lean_IR_FnBody_setBody(x_10, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_12, 0, x_74);
return x_12;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_dec(x_12);
x_76 = lean_ctor_get(x_13, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_77 = x_13;
} else {
 lean_dec_ref(x_13);
 x_77 = lean_box(0);
}
x_78 = l_Lean_IR_FnBody_setBody(x_10, x_76);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_14);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_81 = 1;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_3);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_5);
return x_84;
}
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_inc(x_3);
x_85 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
lean_dec(x_1);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_3);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
return x_89;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_9__D(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_8__Dmain___main(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Init_Lean_Compiler_IR_ResetReuse_5__Dfinalize(x_1, x_2, x_7, x_4, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_ResetReuse_9__D___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_ResetReuse_9__D(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_4);
x_17 = l_Lean_IR_ResetReuse_R___main(x_16, x_4, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_IR_CtorInfo_isScalar(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_inc(x_4);
lean_inc(x_1);
x_22 = l___private_Init_Lean_Compiler_IR_ResetReuse_9__D(x_1, x_15, x_18, x_4, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
x_28 = x_25;
lean_dec(x_11);
x_29 = lean_array_fset(x_14, x_2, x_28);
lean_dec(x_2);
x_2 = x_27;
x_3 = x_29;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_15);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_2, x_31);
x_33 = x_20;
lean_dec(x_11);
x_34 = lean_array_fset(x_14, x_2, x_33);
lean_dec(x_2);
x_2 = x_32;
x_3 = x_34;
x_5 = x_19;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_inc(x_4);
x_37 = l_Lean_IR_ResetReuse_R___main(x_36, x_4, x_5);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_2, x_41);
x_43 = x_40;
lean_dec(x_11);
x_44 = lean_array_fset(x_14, x_2, x_43);
lean_dec(x_2);
x_2 = x_42;
x_3 = x_44;
x_5 = x_39;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ResetReuse_R___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_24 = l_Lean_IR_ResetReuse_R___main(x_22, x_2, x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_20);
x_27 = l_Lean_IR_LocalContext_addJP(x_2, x_20, x_21, x_25);
x_28 = l_Lean_IR_ResetReuse_R___main(x_23, x_27, x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_25);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_1, 3, x_31);
lean_ctor_set(x_1, 2, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
lean_inc(x_2);
x_38 = l_Lean_IR_ResetReuse_R___main(x_36, x_2, x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
lean_inc(x_35);
lean_inc(x_34);
x_41 = l_Lean_IR_LocalContext_addJP(x_2, x_34, x_35, x_39);
x_42 = l_Lean_IR_ResetReuse_R___main(x_37, x_41, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
case 10:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_ctor_get(x_1, 3);
x_51 = lean_unsigned_to_nat(0u);
lean_inc(x_49);
x_52 = l_Array_umapMAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(x_49, x_51, x_50, x_2, x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_1, 3, x_54);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_1, 3, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_ctor_get(x_1, 2);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_62 = lean_unsigned_to_nat(0u);
lean_inc(x_59);
x_63 = l_Array_umapMAux___main___at_Lean_IR_ResetReuse_R___main___spec__1(x_59, x_62, x_61, x_2, x_3);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
default: 
{
lean_object* x_69; 
x_69 = lean_box(0);
x_4 = x_69;
goto block_18;
}
}
block_18:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_IR_FnBody_body(x_1);
x_7 = lean_box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_1, x_7);
x_9 = l_Lean_IR_ResetReuse_R___main(x_6, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_FnBody_setBody(x_8, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_IR_FnBody_setBody(x_8, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
lean_object* l_Lean_IR_ResetReuse_R(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ResetReuse_R___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_7 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_6);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l_Lean_IR_ResetReuse_R___main(x_5, x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_7, x_18);
lean_dec(x_7);
x_20 = lean_box(0);
x_21 = l_Lean_IR_ResetReuse_R___main(x_5, x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 3, x_22);
return x_23;
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Control_State(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_LiveVars(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_ResetReuse(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_LiveVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
