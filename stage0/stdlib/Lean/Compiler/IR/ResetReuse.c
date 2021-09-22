// Lean compiler output
// Module: Lean.Compiler.IR.ResetReuse
// Imports: Init Lean.Compiler.IR.Basic Lean.Compiler.IR.LiveVars Lean.Compiler.IR.Format
#include <lean/lean.h>
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
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_R___boxed__const__1;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___rarg(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_IR_FnBody_hasLiveVar(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_HasIndex_visitFnBody(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_R(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = 1;
x_13 = x_4 + x_12;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_1);
x_16 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_15);
lean_ctor_set(x_11, 1, x_16);
x_17 = x_11;
x_18 = lean_array_uset(x_10, x_4, x_17);
x_4 = x_13;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_1);
x_22 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = x_23;
x_25 = lean_array_uset(x_10, x_4, x_24);
x_4 = x_13;
x_5 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_1);
x_29 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_28);
lean_ctor_set(x_11, 0, x_29);
x_30 = x_11;
x_31 = lean_array_uset(x_10, x_4, x_30);
x_4 = x_13;
x_5 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec(x_11);
lean_inc(x_1);
x_34 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = x_35;
x_37 = lean_array_uset(x_10, x_4, x_36);
x_4 = x_13;
x_5 = x_37;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_ctor_get(x_3, 2);
lean_dec(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_6);
lean_ctor_set(x_3, 3, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
x_16 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_15);
lean_ctor_set(x_3, 2, x_16);
return x_3;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
lean_ctor_set(x_3, 2, x_18);
return x_3;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
x_24 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mayReuse(x_2, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
x_25 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_21);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_21);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_21);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
x_36 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Lean_IR_FnBody_body(x_3);
x_38 = lean_box(13);
x_39 = l_Lean_IR_FnBody_setBody(x_3, x_38);
x_40 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_37);
x_41 = l_Lean_IR_FnBody_setBody(x_39, x_40);
return x_41;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_3, 2);
x_44 = lean_ctor_get(x_3, 3);
lean_inc(x_43);
lean_inc(x_1);
x_45 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_43);
lean_inc(x_45);
lean_inc(x_43);
x_46 = l_Lean_IR_FnBody_beq(x_43, x_45);
if (x_46 == 0)
{
lean_dec(x_43);
lean_dec(x_1);
lean_ctor_set(x_3, 2, x_45);
return x_3;
}
else
{
lean_object* x_47; 
lean_dec(x_45);
x_47 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_44);
lean_ctor_set(x_3, 3, x_47);
return x_3;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = lean_ctor_get(x_3, 1);
x_50 = lean_ctor_get(x_3, 2);
x_51 = lean_ctor_get(x_3, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
lean_inc(x_50);
lean_inc(x_1);
x_52 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_50);
lean_inc(x_52);
lean_inc(x_50);
x_53 = l_Lean_IR_FnBody_beq(x_50, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
x_55 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_51);
x_56 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_55);
return x_56;
}
}
}
case 10:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_3, 3);
x_59 = lean_array_get_size(x_58);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
x_62 = x_58;
x_63 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1(x_1, x_2, x_60, x_61, x_62);
x_64 = x_63;
lean_ctor_set(x_3, 3, x_64);
return x_3;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_3, 0);
x_66 = lean_ctor_get(x_3, 1);
x_67 = lean_ctor_get(x_3, 2);
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_3);
x_69 = lean_array_get_size(x_68);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = 0;
x_72 = x_68;
x_73 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1(x_1, x_2, x_70, x_71, x_72);
x_74 = x_73;
x_75 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_74);
return x_75;
}
}
default: 
{
uint8_t x_76; 
x_76 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lean_IR_FnBody_body(x_3);
x_78 = lean_box(13);
x_79 = l_Lean_IR_FnBody_setBody(x_3, x_78);
x_80 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_77);
x_81 = l_Lean_IR_FnBody_setBody(x_79, x_80);
return x_81;
}
else
{
lean_dec(x_1);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_mkFresh___rarg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_3);
lean_inc(x_8);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_8, x_2, x_3);
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
x_17 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_S(x_15, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_8, x_4, x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_nat_dec_eq(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
goto _start;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(lean_object* x_1, lean_object* x_2) {
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
x_5 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_argsContainsVar(x_4, x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_9 = x_5;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
x_14 = x_11;
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_16, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_18, x_6, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_14, 1, x_21);
x_23 = 1;
x_24 = x_4 + x_23;
x_25 = x_14;
x_26 = lean_array_uset(x_13, x_4, x_25);
x_4 = x_24;
x_5 = x_26;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_29, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_1);
x_33 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_31, x_6, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_34);
x_37 = 1;
x_38 = x_4 + x_37;
x_39 = x_36;
x_40 = lean_array_uset(x_13, x_4, x_39);
x_4 = x_38;
x_5 = x_40;
x_7 = x_35;
goto _start;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_14, 0);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_43, x_6, x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_45, x_6, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_ctor_set(x_14, 0, x_48);
x_50 = 1;
x_51 = x_4 + x_50;
x_52 = x_14;
x_53 = lean_array_uset(x_13, x_4, x_52);
x_4 = x_51;
x_5 = x_53;
x_7 = x_49;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_56 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_55, x_6, x_7);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_1);
x_59 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_57, x_6, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = 1;
x_64 = x_4 + x_63;
x_65 = x_62;
x_66 = lean_array_uset(x_13, x_4, x_65);
x_4 = x_64;
x_5 = x_66;
x_7 = x_61;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_11 = l_Lean_IR_LocalContext_addJP(x_4, x_7, x_8, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_10, x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_9, x_4, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
lean_ctor_set(x_3, 3, x_15);
lean_ctor_set(x_3, 2, x_21);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 0, x_3);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set(x_3, 3, x_15);
lean_ctor_set(x_3, 2, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
lean_ctor_set(x_3, 3, x_15);
lean_ctor_set(x_3, 2, x_27);
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_16);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_3, 2);
x_34 = lean_ctor_get(x_3, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_4);
x_35 = l_Lean_IR_LocalContext_addJP(x_4, x_31, x_32, x_33);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_34, x_35, x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_33, x_4, x_38);
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
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_32);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_39);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
}
case 10:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 3);
lean_inc(x_53);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_3, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_3, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_3, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_3, 0);
lean_dec(x_64);
x_65 = lean_array_get_size(x_53);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = x_53;
x_68 = lean_box_usize(x_66);
x_69 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1;
x_70 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1___boxed), 7, 5);
lean_closure_set(x_70, 0, x_1);
lean_closure_set(x_70, 1, x_2);
lean_closure_set(x_70, 2, x_68);
lean_closure_set(x_70, 3, x_69);
lean_closure_set(x_70, 4, x_67);
x_71 = x_70;
x_72 = lean_apply_2(x_71, x_4, x_5);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_ctor_set(x_3, 3, x_74);
x_76 = 1;
x_77 = lean_box(x_76);
lean_ctor_set(x_72, 1, x_77);
lean_ctor_set(x_72, 0, x_3);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
lean_ctor_set(x_3, 3, x_79);
x_81 = 1;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_3);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
lean_object* x_85; size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_3);
x_85 = lean_array_get_size(x_53);
x_86 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_87 = x_53;
x_88 = lean_box_usize(x_86);
x_89 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1;
x_90 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1___boxed), 7, 5);
lean_closure_set(x_90, 0, x_1);
lean_closure_set(x_90, 1, x_2);
lean_closure_set(x_90, 2, x_88);
lean_closure_set(x_90, 3, x_89);
lean_closure_set(x_90, 4, x_87);
x_91 = x_90;
x_92 = lean_apply_2(x_91, x_4, x_5);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_96, 0, x_50);
lean_ctor_set(x_96, 1, x_51);
lean_ctor_set(x_96, 2, x_52);
lean_ctor_set(x_96, 3, x_93);
x_97 = 1;
x_98 = lean_box(x_97);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_94);
return x_100;
}
}
}
default: 
{
uint8_t x_101; 
x_101 = l_Lean_IR_FnBody_isTerminal(x_3);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = l_Lean_IR_FnBody_body(x_3);
x_103 = lean_box(13);
lean_inc(x_3);
x_104 = l_Lean_IR_FnBody_setBody(x_3, x_103);
x_105 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_isCtorUsing(x_104, x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_106 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_102, x_4, x_5);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_106, 1);
x_112 = lean_ctor_get(x_106, 0);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_107, 0);
x_115 = lean_ctor_get(x_107, 1);
lean_dec(x_115);
lean_inc(x_104);
x_116 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_104);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = l_Lean_IR_FnBody_setBody(x_104, x_114);
lean_ctor_set(x_107, 0, x_117);
return x_106;
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_free_object(x_106);
lean_dec(x_108);
x_118 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_114, x_4, x_111);
lean_dec(x_4);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
x_122 = l_Lean_IR_FnBody_setBody(x_104, x_120);
x_123 = 1;
x_124 = lean_box(x_123);
lean_ctor_set(x_118, 1, x_124);
lean_ctor_set(x_118, 0, x_122);
lean_ctor_set(x_107, 1, x_121);
lean_ctor_set(x_107, 0, x_118);
return x_107;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_118, 0);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_118);
x_127 = l_Lean_IR_FnBody_setBody(x_104, x_125);
x_128 = 1;
x_129 = lean_box(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_107, 1, x_126);
lean_ctor_set(x_107, 0, x_130);
return x_107;
}
}
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_107, 0);
lean_inc(x_131);
lean_dec(x_107);
lean_inc(x_104);
x_132 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_104);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_133 = l_Lean_IR_FnBody_setBody(x_104, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_108);
lean_ctor_set(x_106, 0, x_134);
return x_106;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_106);
lean_dec(x_108);
x_135 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_131, x_4, x_111);
lean_dec(x_4);
lean_dec(x_2);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = l_Lean_IR_FnBody_setBody(x_104, x_136);
x_140 = 1;
x_141 = lean_box(x_140);
if (lean_is_scalar(x_138)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_138;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_137);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_106, 1);
lean_inc(x_144);
lean_dec(x_106);
x_145 = lean_ctor_get(x_107, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_146 = x_107;
} else {
 lean_dec_ref(x_107);
 x_146 = lean_box(0);
}
lean_inc(x_104);
x_147 = l_Lean_IR_HasIndex_visitFnBody(x_1, x_104);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_148 = l_Lean_IR_FnBody_setBody(x_104, x_145);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_146;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_108);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_144);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_108);
x_151 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_tryS(x_1, x_2, x_145, x_4, x_144);
lean_dec(x_4);
lean_dec(x_2);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = l_Lean_IR_FnBody_setBody(x_104, x_152);
x_156 = 1;
x_157 = lean_box(x_156);
if (lean_is_scalar(x_154)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_154;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
if (lean_is_scalar(x_146)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_146;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_153);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_106);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_106, 0);
lean_dec(x_161);
x_162 = !lean_is_exclusive(x_107);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_107, 0);
x_164 = lean_ctor_get(x_107, 1);
lean_dec(x_164);
x_165 = l_Lean_IR_FnBody_setBody(x_104, x_163);
lean_ctor_set(x_107, 0, x_165);
return x_106;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_107, 0);
lean_inc(x_166);
lean_dec(x_107);
x_167 = l_Lean_IR_FnBody_setBody(x_104, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_108);
lean_ctor_set(x_106, 0, x_168);
return x_106;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_106, 1);
lean_inc(x_169);
lean_dec(x_106);
x_170 = lean_ctor_get(x_107, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_171 = x_107;
} else {
 lean_dec_ref(x_107);
 x_171 = lean_box(0);
}
x_172 = l_Lean_IR_FnBody_setBody(x_104, x_170);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_108);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_169);
return x_174;
}
}
}
else
{
uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_175 = 1;
x_176 = lean_box(x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_5);
return x_178;
}
}
else
{
lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_2);
lean_inc(x_3);
x_179 = l_Lean_IR_FnBody_hasLiveVar(x_3, x_4, x_1);
lean_dec(x_1);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
x_181 = lean_box(x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_3);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_5);
return x_183;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dfinalize(x_1, x_2, x_7, x_4, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 < x_2;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = x_4;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_13 = x_10;
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_5);
x_17 = l_Lean_IR_ResetReuse_R(x_16, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_15);
lean_ctor_set(x_13, 1, x_18);
x_20 = l_Lean_IR_CtorInfo_isScalar(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_15);
lean_inc(x_1);
x_21 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(x_1, x_15, x_18, x_5, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
x_25 = 1;
x_26 = x_3 + x_25;
x_27 = x_24;
x_28 = lean_array_uset(x_12, x_3, x_27);
x_3 = x_26;
x_4 = x_28;
x_6 = x_23;
goto _start;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
lean_dec(x_15);
x_30 = 1;
x_31 = x_3 + x_30;
x_32 = x_13;
x_33 = lean_array_uset(x_12, x_3, x_32);
x_3 = x_31;
x_4 = x_33;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
lean_inc(x_5);
x_37 = l_Lean_IR_ResetReuse_R(x_36, x_5, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_38);
lean_inc(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_IR_CtorInfo_isScalar(x_35);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_inc(x_5);
lean_inc(x_35);
lean_inc(x_1);
x_42 = l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_D(x_1, x_35, x_38, x_5, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_43);
x_46 = 1;
x_47 = x_3 + x_46;
x_48 = x_45;
x_49 = lean_array_uset(x_12, x_3, x_48);
x_3 = x_47;
x_4 = x_49;
x_6 = x_44;
goto _start;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_38);
lean_dec(x_35);
x_51 = 1;
x_52 = x_3 + x_51;
x_53 = x_40;
x_54 = lean_array_uset(x_12, x_3, x_53);
x_3 = x_52;
x_4 = x_54;
x_6 = x_39;
goto _start;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_5);
x_58 = l_Lean_IR_ResetReuse_R(x_57, x_5, x_6);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_ctor_set(x_13, 0, x_59);
x_61 = 1;
x_62 = x_3 + x_61;
x_63 = x_13;
x_64 = lean_array_uset(x_12, x_3, x_63);
x_3 = x_62;
x_4 = x_64;
x_6 = x_60;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_66);
lean_dec(x_13);
lean_inc(x_5);
x_67 = l_Lean_IR_ResetReuse_R(x_66, x_5, x_6);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_71 = 1;
x_72 = x_3 + x_71;
x_73 = x_70;
x_74 = lean_array_uset(x_12, x_3, x_73);
x_3 = x_72;
x_4 = x_74;
x_6 = x_69;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ResetReuse_R___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ResetReuse_R(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_9 = l_Lean_IR_ResetReuse_R(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_LocalContext_addJP(x_2, x_5, x_6, x_10);
x_13 = l_Lean_IR_ResetReuse_R(x_8, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set(x_1, 2, x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_2);
x_23 = l_Lean_IR_ResetReuse_R(x_21, x_2, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
x_26 = l_Lean_IR_LocalContext_addJP(x_2, x_19, x_20, x_24);
x_27 = l_Lean_IR_ResetReuse_R(x_22, x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
case 10:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_array_get_size(x_35);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = x_35;
x_39 = lean_box_usize(x_37);
x_40 = l_Lean_IR_ResetReuse_R___boxed__const__1;
lean_inc(x_34);
x_41 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1___boxed), 6, 4);
lean_closure_set(x_41, 0, x_34);
lean_closure_set(x_41, 1, x_39);
lean_closure_set(x_41, 2, x_40);
lean_closure_set(x_41, 3, x_38);
x_42 = x_41;
x_43 = lean_apply_2(x_42, x_2, x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_43, 0, x_1);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
lean_ctor_set(x_1, 3, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_53 = lean_array_get_size(x_52);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = x_52;
x_56 = lean_box_usize(x_54);
x_57 = l_Lean_IR_ResetReuse_R___boxed__const__1;
lean_inc(x_50);
x_58 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1___boxed), 6, 4);
lean_closure_set(x_58, 0, x_50);
lean_closure_set(x_58, 1, x_56);
lean_closure_set(x_58, 2, x_57);
lean_closure_set(x_58, 3, x_55);
x_59 = x_58;
x_60 = lean_apply_2(x_59, x_2, x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_50);
lean_ctor_set(x_64, 2, x_51);
lean_ctor_set(x_64, 3, x_61);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
default: 
{
uint8_t x_66; 
x_66 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = l_Lean_IR_FnBody_body(x_1);
x_68 = lean_box(13);
x_69 = l_Lean_IR_FnBody_setBody(x_1, x_68);
x_70 = l_Lean_IR_ResetReuse_R(x_67, x_2, x_3);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = l_Lean_IR_FnBody_setBody(x_69, x_72);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = l_Lean_IR_FnBody_setBody(x_69, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_3);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_ResetReuse_R___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_4 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = l_Lean_IR_ResetReuse_R(x_2, x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_Decl_updateBody_x21(x_1, x_9);
return x_10;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_LiveVars(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ResetReuse(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LiveVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1 = _init_l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ResetReuse_0__Lean_IR_ResetReuse_Dmain___boxed__const__1);
l_Lean_IR_ResetReuse_R___boxed__const__1 = _init_l_Lean_IR_ResetReuse_R___boxed__const__1();
lean_mark_persistent(l_Lean_IR_ResetReuse_R___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
