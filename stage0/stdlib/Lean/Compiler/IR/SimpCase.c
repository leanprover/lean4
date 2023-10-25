// Lean compiler output
// Module: Lean.Compiler.IR.SimpCase
// Imports: Init Lean.Compiler.IR.Basic Lean.Compiler.IR.Format
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___boxed(lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1(lean_object*, size_t, size_t);
extern lean_object* l_Lean_IR_instInhabitedAlt;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ensureHasDefault(lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_simpCase(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault(lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_IR_Alt_isDefault(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ensureHasDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_13; uint8_t x_14; 
x_2 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
x_3 = x_15;
goto block_12;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_2);
x_18 = l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_3 = x_19;
goto block_12;
}
else
{
lean_dec(x_2);
return x_1;
}
}
block_12:
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_3);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_IR_instInhabitedAlt;
x_7 = l_Array_back___rarg(x_6, x_1);
x_8 = lean_array_pop(x_1);
x_9 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_array_push(x_8, x_10);
return x_11;
}
else
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_dec_lt(x_5, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_IR_instInhabitedAlt;
x_16 = l___private_Init_Util_0__outOfBounds___rarg(x_15);
x_17 = l_Lean_IR_AltCore_body(x_16);
lean_dec(x_16);
lean_inc(x_2);
x_18 = l_Lean_IR_FnBody_beq(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_22 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_22;
x_8 = x_21;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_fget(x_1, x_5);
x_25 = l_Lean_IR_AltCore_body(x_24);
lean_dec(x_24);
lean_inc(x_2);
x_26 = l_Lean_IR_FnBody_beq(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_30 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_30;
x_8 = x_29;
goto _start;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_IR_instInhabitedAlt;
x_4 = lean_array_get(x_3, x_1, x_2);
x_5 = l_Lean_IR_AltCore_body(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_get_size(x_1);
lean_inc(x_8);
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1(x_1, x_5, x_8, x_8, x_7, x_8, x_6, x_6);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_4);
x_16 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_4);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_nat_dec_lt(x_4, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_IR_instInhabitedAlt;
x_22 = l___private_Init_Util_0__outOfBounds___rarg(x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_16);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget(x_1, x_4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_16);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_4);
x_30 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_4);
x_31 = lean_nat_dec_lt(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_33;
x_7 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_35 = lean_nat_dec_lt(x_4, x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_IR_instInhabitedAlt;
x_37 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_39;
x_7 = x_38;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_array_fget(x_1, x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_43;
x_7 = x_42;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_4);
x_16 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_4);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_nat_dec_lt(x_4, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_IR_instInhabitedAlt;
x_22 = l___private_Init_Util_0__outOfBounds___rarg(x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_16);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget(x_1, x_4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_16);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_4);
x_30 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_4);
x_31 = lean_nat_dec_lt(x_28, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_33;
x_7 = x_32;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_35 = lean_nat_dec_lt(x_4, x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_IR_instInhabitedAlt;
x_37 = l___private_Init_Util_0__outOfBounds___rarg(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_39;
x_7 = x_38;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_array_fget(x_1, x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_12;
x_4 = x_43;
x_7 = x_42;
goto _start;
}
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
x_5 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_getOccsOf(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_IR_instInhabitedAlt;
x_7 = l___private_Init_Util_0__outOfBounds___rarg(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_10 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1(x_1, x_2, x_2, x_9, x_2, x_9, x_8);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_array_fget(x_1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2(x_1, x_2, x_2, x_16, x_2, x_16, x_15);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body(x_7);
x_9 = l_Lean_IR_AltCore_body(x_1);
x_10 = l_Lean_IR_FnBody_beq(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_24; uint8_t x_25; 
x_2 = lean_array_get_size(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_le(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_3 = x_28;
goto block_23;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_2);
x_31 = l_Array_anyMUnsafe_any___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_3 = x_32;
goto block_23;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
block_23:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_4 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_maxOccs(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_2);
x_11 = l_Lean_IR_AltCore_body(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_13 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
x_14 = lean_array_push(x_13, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_2, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_16 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
x_17 = lean_array_push(x_16, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_20 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1(x_5, x_1, x_18, x_19, x_20);
lean_dec(x_5);
x_22 = lean_array_push(x_21, x_12);
return x_22;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_AltCore_body(x_6);
x_8 = lean_box(13);
x_9 = l_Lean_IR_FnBody_beq(x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (x_9 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_6);
x_2 = x_11;
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_filterUnreachable(x_4);
x_6 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_IR_instInhabitedAlt;
x_14 = lean_array_get(x_13, x_6, x_8);
lean_dec(x_6);
x_15 = l_Lean_IR_AltCore_body(x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 2);
x_12 = l_Lean_IR_FnBody_simpCase(x_11);
lean_ctor_set(x_5, 2, x_12);
x_13 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_19 = l_Lean_IR_FnBody_simpCase(x_17);
x_20 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_array_uset(x_7, x_2, x_20);
x_2 = x_9;
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; 
x_23 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = l_Lean_IR_FnBody_simpCase(x_11);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = l_Lean_IR_FnBody_simpCase(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_7, x_2, x_18);
x_2 = x_9;
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = l_Lean_IR_FnBody_simpCase(x_22);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = l_Lean_IR_FnBody_simpCase(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_array_uset(x_7, x_2, x_28);
x_2 = x_9;
x_3 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_simpCase(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1(x_6, x_7, x_3);
if (lean_obj_tag(x_4) == 10)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2(x_14, x_7, x_12);
x_16 = l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_mkSimpCase(x_9, x_10, x_11, x_15);
lean_dec(x_15);
x_17 = l_Lean_IR_reshape(x_8, x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_IR_reshape(x_8, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_simpCase___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_simpCase(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_simpCase(x_2);
x_4 = l_Lean_IR_Decl_updateBody_x21(x_1, x_3);
return x_4;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1 = _init_l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_SimpCase_0__Lean_IR_addDefault___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
