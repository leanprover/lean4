// Lean compiler output
// Module: Init.Lean.Compiler.IR.PushProj
// Imports: Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.FreeVars Init.Lean.Compiler.IR.NormIds
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
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj___main(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj(lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Lean_IR_mkIndexSet(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_vsetInh;
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
extern lean_object* l_Array_umapMAux___main___rarg___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = x_5;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_5, x_4);
x_10 = l_Array_umapMAux___main___rarg___closed__1;
x_11 = lean_array_fset(x_5, x_4, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
x_16 = l_Lean_IR_vsetInh;
x_17 = lean_array_get(x_16, x_1, x_4);
x_18 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_17, x_3);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = x_9;
x_20 = lean_array_fset(x_11, x_4, x_19);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_inc(x_2);
x_22 = l_Lean_IR_FnBody_setBody(x_2, x_15);
lean_ctor_set(x_9, 1, x_22);
x_23 = x_9;
x_24 = lean_array_fset(x_11, x_4, x_23);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = l_Lean_IR_vsetInh;
x_29 = lean_array_get(x_28, x_1, x_4);
x_30 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_29, x_3);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_32 = x_31;
x_33 = lean_array_fset(x_11, x_4, x_32);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_30);
lean_inc(x_2);
x_35 = l_Lean_IR_FnBody_setBody(x_2, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_37 = x_36;
x_38 = lean_array_fset(x_11, x_4, x_37);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = l_Lean_IR_vsetInh;
x_43 = lean_array_get(x_42, x_1, x_4);
x_44 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_43, x_3);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = x_9;
x_46 = lean_array_fset(x_11, x_4, x_45);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
lean_inc(x_2);
x_48 = l_Lean_IR_FnBody_setBody(x_2, x_41);
lean_ctor_set(x_9, 0, x_48);
x_49 = x_9;
x_50 = lean_array_fset(x_11, x_4, x_49);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_50;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_9, 0);
lean_inc(x_52);
lean_dec(x_9);
x_53 = l_Lean_IR_vsetInh;
x_54 = lean_array_get(x_53, x_1, x_4);
x_55 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_54, x_3);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_52);
x_57 = x_56;
x_58 = lean_array_fset(x_11, x_4, x_57);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
lean_inc(x_2);
x_60 = l_Lean_IR_FnBody_setBody(x_2, x_52);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = x_61;
x_63 = lean_array_fset(x_11, x_4, x_62);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_63;
goto _start;
}
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = l_Array_umapMAux___main___rarg___closed__1;
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
x_13 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_8, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = x_8;
x_15 = lean_array_fset(x_10, x_3, x_14);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_inc(x_1);
x_17 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_8);
x_18 = x_17;
x_19 = lean_array_fset(x_10, x_3, x_18);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_19;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_pushProjs___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_1);
x_8 = lean_array_pop(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_7, 2);
lean_inc(x_31);
switch (lean_obj_tag(x_31)) {
case 3:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
x_21 = x_32;
x_22 = x_33;
x_23 = x_31;
goto block_30;
}
case 4:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
x_21 = x_34;
x_22 = x_35;
x_23 = x_31;
goto block_30;
}
case 5:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
x_21 = x_36;
x_22 = x_37;
x_23 = x_31;
goto block_30;
}
case 12:
{
lean_object* x_38; 
lean_dec(x_31);
x_38 = lean_box(0);
x_16 = x_38;
goto block_20;
}
case 13:
{
lean_object* x_39; 
lean_dec(x_31);
x_39 = lean_box(0);
x_16 = x_39;
goto block_20;
}
default: 
{
lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_3);
x_40 = lean_box(0);
x_9 = x_40;
goto block_15;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_3);
x_41 = lean_box(0);
x_9 = x_41;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_10 = lean_array_push(x_8, x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_reverseAux___main___rarg(x_4, x_11);
x_13 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_12, x_12, x_11, x_10);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
block_20:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
lean_inc(x_7);
x_17 = lean_array_push(x_4, x_7);
x_18 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
block_30:
{
lean_object* x_24; 
lean_dec(x_23);
lean_dec(x_22);
x_24 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
x_26 = l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2(x_3, x_7, x_21, x_25, x_2);
x_27 = l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3(x_7, x_21, x_25, x_3);
lean_dec(x_21);
x_1 = x_8;
x_2 = x_26;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_21);
x_29 = lean_box(0);
x_16 = x_29;
goto block_20;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_reverseAux___main___rarg(x_4, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
return x_44;
}
}
}
lean_object* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_IR_pushProjs___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_IR_pushProjs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_pushProjs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = l_Array_umapMAux___main___rarg___closed__1;
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_6, 2);
x_18 = l_Lean_IR_FnBody_pushProj___main(x_17);
lean_ctor_set(x_6, 2, x_18);
x_11 = x_6;
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_23 = l_Lean_IR_FnBody_pushProj___main(x_21);
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_11 = x_24;
goto block_15;
}
}
else
{
x_11 = x_6;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = x_11;
x_13 = lean_array_fset(x_8, x_1, x_12);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_13;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = l_Array_umapMAux___main___rarg___closed__1;
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_10 = l_Lean_IR_FnBody_freeIndices(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = l_Array_umapMAux___main___rarg___closed__1;
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = l_Lean_IR_FnBody_pushProj___main(x_12);
lean_ctor_set(x_6, 1, x_13);
x_14 = x_6;
x_15 = lean_array_fset(x_8, x_1, x_14);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = l_Lean_IR_FnBody_pushProj___main(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = x_20;
x_22 = lean_array_fset(x_8, x_1, x_21);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = l_Lean_IR_FnBody_pushProj___main(x_25);
lean_ctor_set(x_6, 0, x_26);
x_27 = x_6;
x_28 = lean_array_fset(x_8, x_1, x_27);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
x_31 = l_Lean_IR_FnBody_pushProj___main(x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = x_32;
x_34 = lean_array_fset(x_8, x_1, x_33);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_34;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_FnBody_pushProj___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(x_5, x_3);
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_5, x_9);
lean_inc(x_8);
x_11 = l_Lean_IR_mkIndexSet(x_8);
x_12 = l_Array_empty___closed__1;
x_13 = l_Lean_IR_pushProjs___main(x_6, x_9, x_10, x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_5, x_15);
lean_ctor_set(x_4, 3, x_16);
x_17 = l_Lean_IR_reshape(x_14, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_21);
x_22 = l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_5, x_21);
lean_inc(x_19);
x_23 = l_Lean_IR_mkIndexSet(x_19);
x_24 = l_Array_empty___closed__1;
x_25 = l_Lean_IR_pushProjs___main(x_6, x_21, x_22, x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_umapMAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_5, x_27);
x_29 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Lean_IR_reshape(x_26, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_IR_reshape(x_6, x_4);
return x_31;
}
}
}
lean_object* l_Lean_IR_FnBody_pushProj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_FnBody_pushProj___main(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_pushProj(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_IR_FnBody_pushProj___main(x_3);
lean_ctor_set(x_1, 3, x_4);
x_5 = l_Lean_IR_Decl_normalizeIds(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = l_Lean_IR_FnBody_pushProj___main(x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
x_12 = l_Lean_IR_Decl_normalizeIds(x_11);
return x_12;
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_FreeVars(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_PushProj(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
