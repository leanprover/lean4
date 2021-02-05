// Lean compiler output
// Module: Lean.Compiler.IR.PushProj
// Imports: Init Lean.Compiler.IR.Basic Lean.Compiler.IR.FreeVars Lean.Compiler.IR.NormIds
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
lean_object* l_Lean_IR_FnBody_pushProj_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_IR_Decl_pushProj_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_IR_pushProjs___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_pushProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3(size_t, size_t, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_pushProjs___spec__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2(size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj_match__2(lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj(lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
lean_object* l_Lean_IR_Decl_pushProj_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs_match__2(lean_object*);
lean_object* l_Lean_IR_FnBody_pushProj_match__3(lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1(size_t, size_t, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mapIdxM_map_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Lean_IR_mkIndexSet(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedIndexSet;
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
lean_object* l_Lean_IR_pushProjs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_3, x_11, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_3(x_4, x_14, x_15, x_16);
return x_17;
}
case 12:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_5, x_18);
return x_19;
}
case 13:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_1(x_6, x_20);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_apply_1(x_7, x_1);
return x_22;
}
}
}
}
lean_object* l_Lean_IR_pushProjs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_pushProjs_match__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_IR_pushProjs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_IR_pushProjs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_pushProjs_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_back___at_Lean_IR_pushProjs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_instInhabitedFnBody;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = l_Lean_IR_instInhabitedIndexSet;
x_16 = lean_array_get(x_15, x_3, x_2);
x_17 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_16, x_4);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_5, x_10);
x_19 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_inc(x_7);
x_20 = l_Lean_IR_FnBody_setBody(x_7, x_14);
lean_ctor_set(x_10, 1, x_20);
x_21 = lean_array_push(x_5, x_10);
x_22 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_IR_instInhabitedIndexSet;
x_26 = lean_array_get(x_25, x_3, x_2);
x_27 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_26, x_4);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_push(x_5, x_28);
x_30 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_inc(x_7);
x_31 = l_Lean_IR_FnBody_setBody(x_7, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_5, x_32);
x_34 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = l_Lean_IR_instInhabitedIndexSet;
x_38 = lean_array_get(x_37, x_3, x_2);
x_39 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_array_push(x_5, x_10);
x_41 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_inc(x_7);
x_42 = l_Lean_IR_FnBody_setBody(x_7, x_36);
lean_ctor_set(x_10, 0, x_42);
x_43 = lean_array_push(x_5, x_10);
x_44 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
lean_dec(x_10);
x_46 = l_Lean_IR_instInhabitedIndexSet;
x_47 = lean_array_get(x_46, x_3, x_2);
x_48 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_47, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = lean_array_push(x_5, x_49);
x_51 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_inc(x_7);
x_52 = l_Lean_IR_FnBody_setBody(x_7, x_45);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_array_push(x_5, x_53);
x_55 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_54);
return x_55;
}
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1___boxed), 9, 7);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_1);
lean_closure_set(x_11, 6, x_3);
x_12 = l_Array_mapIdxM_map_match__1___rarg(x_6, lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = 1;
x_13 = x_4 + x_12;
x_14 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_11, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = x_11;
x_16 = lean_array_uset(x_10, x_4, x_15);
x_4 = x_13;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_11);
x_19 = x_18;
x_20 = lean_array_uset(x_10, x_4, x_19);
x_4 = x_13;
x_5 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = l_Lean_IR_instInhabitedIndexSet;
x_16 = lean_array_get(x_15, x_3, x_2);
x_17 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_16, x_4);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_5, x_10);
x_19 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_inc(x_7);
x_20 = l_Lean_IR_FnBody_setBody(x_7, x_14);
lean_ctor_set(x_10, 1, x_20);
x_21 = lean_array_push(x_5, x_10);
x_22 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_IR_instInhabitedIndexSet;
x_26 = lean_array_get(x_25, x_3, x_2);
x_27 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_26, x_4);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_push(x_5, x_28);
x_30 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_inc(x_7);
x_31 = l_Lean_IR_FnBody_setBody(x_7, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_5, x_32);
x_34 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = l_Lean_IR_instInhabitedIndexSet;
x_38 = lean_array_get(x_37, x_3, x_2);
x_39 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_array_push(x_5, x_10);
x_41 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_inc(x_7);
x_42 = l_Lean_IR_FnBody_setBody(x_7, x_36);
lean_ctor_set(x_10, 0, x_42);
x_43 = lean_array_push(x_5, x_10);
x_44 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
lean_dec(x_10);
x_46 = l_Lean_IR_instInhabitedIndexSet;
x_47 = lean_array_get(x_46, x_3, x_2);
x_48 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_47, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = lean_array_push(x_5, x_49);
x_51 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_inc(x_7);
x_52 = l_Lean_IR_FnBody_setBody(x_7, x_45);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_array_push(x_5, x_53);
x_55 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_54);
return x_55;
}
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1___boxed), 9, 7);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_1);
lean_closure_set(x_11, 6, x_3);
x_12 = l_Array_mapIdxM_map_match__1___rarg(x_6, lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = 1;
x_13 = x_4 + x_12;
x_14 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_11, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = x_11;
x_16 = lean_array_uset(x_10, x_4, x_15);
x_4 = x_13;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_11);
x_19 = x_18;
x_20 = lean_array_uset(x_10, x_4, x_19);
x_4 = x_13;
x_5 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = l_Lean_IR_instInhabitedIndexSet;
x_16 = lean_array_get(x_15, x_3, x_2);
x_17 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_16, x_4);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_push(x_5, x_10);
x_19 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_inc(x_7);
x_20 = l_Lean_IR_FnBody_setBody(x_7, x_14);
lean_ctor_set(x_10, 1, x_20);
x_21 = lean_array_push(x_5, x_10);
x_22 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_IR_instInhabitedIndexSet;
x_26 = lean_array_get(x_25, x_3, x_2);
x_27 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_26, x_4);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_push(x_5, x_28);
x_30 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_inc(x_7);
x_31 = l_Lean_IR_FnBody_setBody(x_7, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_5, x_32);
x_34 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = l_Lean_IR_instInhabitedIndexSet;
x_38 = lean_array_get(x_37, x_3, x_2);
x_39 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_array_push(x_5, x_10);
x_41 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_inc(x_7);
x_42 = l_Lean_IR_FnBody_setBody(x_7, x_36);
lean_ctor_set(x_10, 0, x_42);
x_43 = lean_array_push(x_5, x_10);
x_44 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
lean_dec(x_10);
x_46 = l_Lean_IR_instInhabitedIndexSet;
x_47 = lean_array_get(x_46, x_3, x_2);
x_48 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_47, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = lean_array_push(x_5, x_49);
x_51 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_inc(x_7);
x_52 = l_Lean_IR_FnBody_setBody(x_7, x_45);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_array_push(x_5, x_53);
x_55 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_6, x_3, x_7, x_4, x_1, x_8, x_12, lean_box(0), x_54);
return x_55;
}
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Array_mapIdx___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1___boxed), 9, 7);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_1);
lean_closure_set(x_11, 6, x_3);
x_12 = l_Array_mapIdxM_map_match__1___rarg(x_6, lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = 1;
x_13 = x_4 + x_12;
x_14 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_11, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = x_11;
x_16 = lean_array_uset(x_10, x_4, x_15);
x_4 = x_13;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_11);
x_19 = x_18;
x_20 = lean_array_uset(x_10, x_4, x_19);
x_4 = x_13;
x_5 = x_20;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_pushProjs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_back___at_Lean_IR_pushProjs___spec__1(x_1);
x_8 = lean_array_pop(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 3:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_2, x_3, x_7, x_10, x_2, x_12, x_14, lean_box(0), x_13);
lean_dec(x_12);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_3;
x_20 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3(x_7, x_10, x_17, x_18, x_19);
lean_dec(x_10);
x_21 = x_20;
x_1 = x_8;
x_2 = x_15;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_inc(x_7);
x_23 = lean_array_push(x_4, x_7);
x_24 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_23;
x_5 = x_24;
goto _start;
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_array_get_size(x_2);
x_29 = lean_mk_empty_array_with_capacity(x_28);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_2, x_3, x_7, x_26, x_2, x_28, x_30, lean_box(0), x_29);
lean_dec(x_28);
x_32 = lean_array_get_size(x_3);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = x_3;
x_36 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5(x_7, x_26, x_33, x_34, x_35);
lean_dec(x_26);
x_37 = x_36;
x_1 = x_8;
x_2 = x_31;
x_3 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
lean_dec(x_26);
lean_inc(x_7);
x_39 = lean_array_push(x_4, x_7);
x_40 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_39;
x_5 = x_40;
goto _start;
}
}
case 5:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
x_43 = l_Std_RBNode_findCore___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_array_get_size(x_2);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_unsigned_to_nat(0u);
lean_inc(x_42);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_2, x_3, x_7, x_42, x_2, x_44, x_46, lean_box(0), x_45);
lean_dec(x_44);
x_48 = lean_array_get_size(x_3);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = 0;
x_51 = x_3;
x_52 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7(x_7, x_42, x_49, x_50, x_51);
lean_dec(x_42);
x_53 = x_52;
x_1 = x_8;
x_2 = x_47;
x_3 = x_53;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_42);
lean_inc(x_7);
x_55 = lean_array_push(x_4, x_7);
x_56 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_55;
x_5 = x_56;
goto _start;
}
}
case 12:
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_9);
lean_inc(x_7);
x_58 = lean_array_push(x_4, x_7);
x_59 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_58;
x_5 = x_59;
goto _start;
}
case 13:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_9);
lean_inc(x_7);
x_61 = lean_array_push(x_4, x_7);
x_62 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_61;
x_5 = x_62;
goto _start;
}
default: 
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_64 = lean_array_push(x_8, x_7);
x_65 = l_Array_reverse___rarg(x_4);
x_66 = l_Array_append___rarg(x_64, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_2);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_5);
lean_dec(x_3);
x_68 = lean_array_push(x_8, x_7);
x_69 = l_Array_reverse___rarg(x_4);
x_70 = l_Array_append___rarg(x_68, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_2);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_72 = l_Array_reverse___rarg(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_2);
return x_73;
}
}
}
lean_object* l_Array_back___at_Lean_IR_pushProjs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_pushProjs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapIdxM_map___at_Lean_IR_pushProjs___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_pushProjs___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_pushProj_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_pushProj_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_FnBody_pushProj_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_pushProj_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 2);
x_19 = l_Lean_IR_FnBody_pushProj(x_18);
lean_ctor_set(x_9, 2, x_19);
x_12 = x_9;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_24 = l_Lean_IR_FnBody_pushProj(x_22);
x_25 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_23);
x_12 = x_25;
goto block_16;
}
}
else
{
x_12 = x_9;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = x_12;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_11;
x_3 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_FnBody_freeIndices(x_10);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = l_Lean_IR_FnBody_pushProj(x_13);
lean_ctor_set(x_9, 1, x_14);
x_15 = x_9;
x_16 = lean_array_uset(x_8, x_2, x_15);
x_2 = x_11;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l_Lean_IR_FnBody_pushProj(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = x_21;
x_23 = lean_array_uset(x_8, x_2, x_22);
x_2 = x_11;
x_3 = x_23;
goto _start;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = l_Lean_IR_FnBody_pushProj(x_26);
lean_ctor_set(x_9, 0, x_27);
x_28 = x_9;
x_29 = lean_array_uset(x_8, x_2, x_28);
x_2 = x_11;
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_9, 0);
lean_inc(x_31);
lean_dec(x_9);
x_32 = l_Lean_IR_FnBody_pushProj(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = x_33;
x_35 = lean_array_uset(x_8, x_2, x_34);
x_2 = x_11;
x_3 = x_35;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_FnBody_pushProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
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
x_8 = x_3;
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1(x_6, x_7, x_8);
x_10 = x_9;
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_13);
x_16 = x_13;
x_17 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2(x_15, x_7, x_16);
x_18 = x_17;
lean_inc(x_12);
x_19 = l_Lean_IR_mkIndexSet(x_12);
x_20 = l_Array_empty___closed__1;
x_21 = l_Lean_IR_pushProjs(x_10, x_13, x_18, x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = x_23;
x_27 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3(x_25, x_7, x_26);
x_28 = x_27;
lean_ctor_set(x_4, 3, x_28);
x_29 = l_Lean_IR_reshape(x_22, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_4, 2);
x_33 = lean_ctor_get(x_4, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_34 = lean_array_get_size(x_33);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
lean_inc(x_33);
x_36 = x_33;
x_37 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2(x_35, x_7, x_36);
x_38 = x_37;
lean_inc(x_31);
x_39 = l_Lean_IR_mkIndexSet(x_31);
x_40 = l_Array_empty___closed__1;
x_41 = l_Lean_IR_pushProjs(x_10, x_33, x_38, x_40, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = x_43;
x_47 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3(x_45, x_7, x_46);
x_48 = x_47;
x_49 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_49, 0, x_30);
lean_ctor_set(x_49, 1, x_31);
lean_ctor_set(x_49, 2, x_32);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_IR_reshape(x_42, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
x_51 = l_Lean_IR_reshape(x_10, x_4);
return x_51;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__2(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_pushProj___spec__3(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_IR_Decl_pushProj_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_IR_Decl_pushProj_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Decl_pushProj_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_pushProj(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_pushProj(x_2);
x_4 = l_Lean_IR_Decl_updateBody_x21(x_1, x_3);
x_5 = l_Lean_IR_Decl_normalizeIds(x_4);
return x_5;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_PushProj(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
