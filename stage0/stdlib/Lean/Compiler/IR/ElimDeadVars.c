// Lean compiler output
// Module: Lean.Compiler.IR.ElimDeadVars
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.FreeVars
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
LEAN_EXPORT lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1(size_t, size_t, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* l_Lean_IR_FnBody_freeIndices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_IR_FnBody_collectFreeIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_2);
x_7 = l_Lean_IR_FnBody_setBody(x_1, x_3);
x_8 = l_Lean_IR_reshapeWithoutDead_reshape(x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; 
x_5 = lean_box(13);
x_6 = l_Array_back_x21___redArg(x_5, x_1);
x_7 = lean_array_pop(x_1);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_11 = x_15;
goto block_14;
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_11 = x_16;
goto block_14;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_IR_reshapeWithoutDead_reshape___lam__0(x_6, x_3, x_2, x_7, x_17);
return x_18;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_IR_reshapeWithoutDead_reshape___lam__0(x_6, x_3, x_2, x_7, x_8);
return x_9;
}
block_14:
{
lean_object* x_12; 
x_12 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_FreeVars_0__Lean_IR_FreeIndices_collectArg_spec__0___redArg(x_3, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
if (x_4 == 0)
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
else
{
goto block_10;
}
}
else
{
lean_dec(x_12);
goto block_10;
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
LEAN_EXPORT lean_object* l_Lean_IR_reshapeWithoutDead_reshape___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_reshapeWithoutDead_reshape___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_16 = l_Lean_IR_FnBody_elimDead(x_15);
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
x_21 = l_Lean_IR_FnBody_elimDead(x_19);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_16 = l_Lean_IR_FnBody_elimDead(x_15);
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
x_19 = l_Lean_IR_FnBody_elimDead(x_18);
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
x_23 = l_Lean_IR_FnBody_elimDead(x_22);
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
x_25 = l_Lean_IR_FnBody_elimDead(x_24);
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
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_elimDead(lean_object* x_1) {
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
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0(x_5, x_6, x_3);
if (lean_obj_tag(x_4) == 10)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1(x_10, x_6, x_9);
lean_ctor_set(x_4, 3, x_11);
x_12 = l_Lean_IR_reshapeWithoutDead(x_7, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_17 = lean_array_size(x_16);
x_18 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1(x_17, x_6, x_16);
x_19 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean_IR_reshapeWithoutDead(x_7, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_IR_reshapeWithoutDead(x_7, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_FnBody_elimDead_spec__1(x_4, x_5, x_3);
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
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
