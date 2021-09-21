// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadVars
// Imports: Init Lean.Compiler.IR.Basic Lean.Compiler.IR.FreeVars
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
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1(lean_object*);
lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2(size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1___boxed(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1(x_1);
x_6 = lean_array_pop(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_3, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_inc(x_5);
x_10 = l_Lean_IR_FnBody_collectFreeIndices(x_5, x_3);
x_11 = l_Lean_IR_FnBody_setBody(x_5, x_2);
x_1 = x_6;
x_2 = x_11;
x_3 = x_10;
goto _start;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = l_Std_RBNode_findCore___at___private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectIndex___spec__1(x_3, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_inc(x_5);
x_16 = l_Lean_IR_FnBody_collectFreeIndices(x_5, x_3);
x_17 = l_Lean_IR_FnBody_setBody(x_5, x_2);
x_1 = x_6;
x_2 = x_17;
x_3 = x_16;
goto _start;
}
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_5);
x_19 = l_Lean_IR_FnBody_collectFreeIndices(x_5, x_3);
x_20 = l_Lean_IR_FnBody_setBody(x_5, x_2);
x_1 = x_6;
x_2 = x_20;
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_reshapeWithoutDead_reshape___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_freeIndices(x_2);
x_4 = l_Lean_IR_reshapeWithoutDead_reshape(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_19 = l_Lean_IR_FnBody_elimDead(x_18);
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
x_24 = l_Lean_IR_FnBody_elimDead(x_22);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_14 = l_Lean_IR_FnBody_elimDead(x_13);
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
x_20 = l_Lean_IR_FnBody_elimDead(x_19);
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
x_27 = l_Lean_IR_FnBody_elimDead(x_26);
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
x_32 = l_Lean_IR_FnBody_elimDead(x_31);
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
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object* x_1) {
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
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1(x_6, x_7, x_8);
x_10 = x_9;
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = x_12;
x_16 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2(x_14, x_7, x_15);
x_17 = x_16;
lean_ctor_set(x_4, 3, x_17);
x_18 = l_Lean_IR_reshapeWithoutDead(x_10, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 2);
x_22 = lean_ctor_get(x_4, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = x_22;
x_26 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2(x_24, x_7, x_25);
x_27 = x_26;
x_28 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Lean_IR_reshapeWithoutDead(x_10, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_IR_reshapeWithoutDead(x_10, x_4);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_FnBody_elimDead___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_elimDead(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_Lean_IR_FnBody_elimDead(x_2);
x_4 = l_Lean_IR_Decl_updateBody_x21(x_1, x_3);
return x_4;
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
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(lean_object* w) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
