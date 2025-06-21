// Lean compiler output
// Module: Lean.Compiler.IR.PushProj
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.FreeVars Lean.Compiler.IR.NormIds
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2(size_t, size_t, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pushProj(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0(size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_IR_mkIndexSet(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1(size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_IR_FnBody_pushProj___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_array_get(x_6, x_1, x_2);
x_8 = l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(x_7, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_9; 
lean_dec(x_8);
x_9 = l_Lean_IR_FnBody_setBody(x_4, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_17 = lean_array_fget(x_4, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_3);
x_20 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(x_1, x_6, x_2, x_3, x_19);
lean_ctor_set(x_17, 1, x_20);
x_12 = x_17;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_3);
x_23 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(x_1, x_6, x_2, x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_12 = x_24;
goto block_16;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_3);
x_27 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(x_1, x_6, x_2, x_3, x_26);
lean_ctor_set(x_17, 0, x_27);
x_12 = x_17;
goto block_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
lean_inc(x_3);
x_29 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(x_1, x_6, x_2, x_3, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_12 = x_30;
goto block_16;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_14 = lean_array_push(x_7, x_12);
x_5 = x_11;
x_6 = x_13;
x_7 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_16 = l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(x_7, x_1);
if (lean_obj_tag(x_16) == 0)
{
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_17; 
lean_dec(x_16);
lean_inc(x_2);
x_17 = l_Lean_IR_FnBody_collectFreeIndices(x_2, x_7);
x_10 = x_17;
goto block_15;
}
block_15:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_8 = lean_array_push(x_1, x_2);
x_9 = l_Lean_IR_FnBody_collectFreeIndices(x_2, x_3);
x_10 = l_Lean_IR_pushProjs(x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___redArg(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(13);
x_8 = l_Array_back_x21___redArg(x_7, x_1);
x_9 = lean_array_pop(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 2);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 3:
{
lean_dec(x_26);
goto block_32;
}
case 4:
{
lean_dec(x_26);
goto block_32;
}
case 5:
{
lean_dec(x_26);
goto block_32;
}
case 12:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = l_Lean_IR_pushProjs___lam__0(x_4, x_8, x_5, x_9, x_2, x_3, x_33);
return x_34;
}
default: 
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
goto block_24;
}
}
block_30:
{
if (x_6 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = l_Lean_IR_pushProjs___lam__0(x_4, x_8, x_5, x_9, x_2, x_3, x_28);
return x_29;
}
else
{
x_10 = x_27;
goto block_19;
}
}
block_32:
{
lean_object* x_31; 
x_31 = l_Lean_RBNode_findCore___at___Lean_IR_UniqueIds_checkId_spec__0___redArg(x_5, x_25);
if (lean_obj_tag(x_31) == 0)
{
if (x_6 == 0)
{
x_10 = x_25;
goto block_19;
}
else
{
x_27 = x_25;
goto block_30;
}
}
else
{
lean_dec(x_31);
x_27 = x_25;
goto block_30;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
goto block_24;
}
block_19:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_11);
lean_inc(x_8);
x_14 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg(x_3, x_10, x_8, x_2, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_array_size(x_3);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1(x_10, x_8, x_15, x_16, x_3);
lean_dec(x_10);
x_1 = x_9;
x_2 = x_14;
x_3 = x_17;
goto _start;
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_push(x_9, x_8);
x_21 = l_Array_reverse___redArg(x_4);
x_22 = l_Array_append___redArg(x_20, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_35 = l_Array_reverse___redArg(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___Lean_IR_pushProjs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_pushProjs_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_pushProjs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_pushProjs___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 2);
x_16 = l_Lean_IR_FnBody_pushProj(x_15);
lean_ctor_set(x_5, 2, x_16);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_21 = l_Lean_IR_FnBody_pushProj(x_19);
x_22 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_20);
x_8 = x_22;
goto block_13;
}
}
else
{
x_8 = x_5;
goto block_13;
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = l_Lean_IR_FnBody_freeIndices(x_14);
x_8 = x_15;
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Lean_IR_FnBody_freeIndices(x_16);
x_8 = x_17;
goto block_13;
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = l_Lean_IR_FnBody_pushProj(x_15);
lean_ctor_set(x_5, 1, x_16);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = l_Lean_IR_FnBody_pushProj(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_8 = x_20;
goto block_13;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = l_Lean_IR_FnBody_pushProj(x_22);
lean_ctor_set(x_5, 0, x_23);
x_8 = x_5;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_IR_FnBody_pushProj(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_8 = x_26;
goto block_13;
}
}
block_13:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_FnBody_pushProj___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_pushProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0(x_5, x_6, x_3);
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_array_size(x_10);
lean_inc(x_10);
x_12 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1(x_11, x_6, x_10);
x_13 = l_Lean_IR_FnBody_pushProj___closed__0;
lean_inc(x_9);
x_14 = l_Lean_IR_mkIndexSet(x_9);
x_15 = l_Lean_IR_pushProjs(x_7, x_10, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2(x_18, x_6, x_17);
lean_ctor_set(x_4, 3, x_19);
x_20 = l_Lean_IR_reshape(x_16, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_25 = lean_array_size(x_24);
lean_inc(x_24);
x_26 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1(x_25, x_6, x_24);
x_27 = l_Lean_IR_FnBody_pushProj___closed__0;
lean_inc(x_22);
x_28 = l_Lean_IR_mkIndexSet(x_22);
x_29 = l_Lean_IR_pushProjs(x_7, x_24, x_26, x_27, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2(x_32, x_6, x_31);
x_34 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_33);
x_35 = l_Lean_IR_reshape(x_30, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = l_Lean_IR_reshape(x_7, x_4);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_pushProj_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_pushProj(lean_object* x_1) {
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
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_PushProj(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_FnBody_pushProj___closed__0 = _init_l_Lean_IR_FnBody_pushProj___closed__0();
lean_mark_persistent(l_Lean_IR_FnBody_pushProj___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
